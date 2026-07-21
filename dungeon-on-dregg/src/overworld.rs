//! # `overworld` — the CONNECTIVE layer: N standalone universes become ONE navigable REGION.
//!
//! Each committed universe in this crate ([`crate::deploy_keep`], [`crate::deploy_vault`],
//! [`crate::deploy_bazaar`], [`crate::deploy_crypt`], …) is an independently-verifiable dungeon on
//! the REAL `spween-dregg` executor: a move is one cap-bounded `TurnReceipt`, an illegal move is a
//! real `WorldError::Refused`, and a stranger re-verifies the whole chain by replay
//! ([`spween_dregg::verify`]). This module is the layer ABOVE them — a [`RegionMap`] of named
//! [`Loc`]ations (each a universe) joined by travel edges, opened as you honestly clear them.
//!
//! This is the salvage of `attested-dm/src/overworld.rs`'s PROVEN design (a `Region` of dungeons
//! joined by travel `Edge`s, travel gated on VERIFIED COMPLETION) RE-HOMED off attested-dm's toy
//! blake3 ledger onto the real substrate: the map is a real dregg [`RegionCell`] with real executor
//! teeth, and completing a dungeon is a real committed turn that unlocks the next.
//!
//! ## The map is a real cell; the travel gate is a real executor predicate
//!
//! A [`RegionCell`] is ONE dregg cell on an [`EmbeddedExecutor`] (the exact primitive
//! [`crate::multicell`] uses). Its owned state carries a `current_location` marker and a
//! WRITE-ONCE `cleared` flag PER location. Its installed [`CellProgram::Cases`] program gives it two
//! kinds of teeth the verified executor re-checks on every touching turn:
//!
//! * **`travel/<dest>`** — admitted IFF `cleared[prereq(dest)] >= 1` (a real
//!   [`StateConstraint::FieldGte`] on the prerequisite's cleared flag). Before the prerequisite is
//!   cleared the executor REFUSES the travel turn in-band — nothing commits (anti-ghost). This is
//!   the load-bearing tooth: **the road opens only once you have honestly cleared the way to it.**
//! * **`clear/<loc>`** — sets `cleared[loc] = 1` under a [`StateConstraint::WriteOnce`] (a cleared
//!   flag can never be un-set or re-forged to a different value). A `clear` presented under ANY
//!   OTHER method is a real executor refusal (a `Cases` program is default-deny —
//!   `NoTransitionCaseMatched` — so a flag written outside the sanctioned method fails closed). See
//!   [`RegionCell::forge_cleared`] + the driven forged-flag test.
//!
//! ## How "verified completion" is bound to the unlock — a SESSION-level binding (named)
//!
//! The `clear/<loc>` turn is fired by the offering layer ([`dreggnet_offerings`]'s
//! `OverworldOffering`) ONLY when the location's universe has been genuinely PLAYED TO A WIN and its
//! playthrough re-verifies by replay ([`reverify_win`]) — the SAME `Won + verify + replay` gate the
//! attested-dm design's `record_completion` used, now producing a real committed region-cell turn
//! instead of a `BTreeSet` insert. This binding lives at the session level (like
//! [`crate::progression`]'s XP grant, which fires a real character-cell turn only on a real landed
//! dungeon outcome). The PURIST alternative — the region cell gating `clear` on the dungeon cell's
//! finalized WIN root through a cross-cell [`StateConstraint::ObservedFieldEquals`] (the
//! [`crate::multicell`] pattern) — needs the region cell and the dungeon `WorldCell`s to share ONE
//! executor ledger (a `WorldCell` privately owns its executor), so it is a named follow-up. What is
//! REAL here: the travel gate, the WriteOnce cleared flag, the default-deny forged-method refusal,
//! and the per-dungeon replay are all executor-enforced.
//!
//! ## Honest scope
//!
//! * Region progress is the live [`RegionCell`] state in-process; the durable per-identity store is
//!   the character store's job (a named follow-up, exactly as [`crate::progression`]'s sheet is).
//! * The concrete [`deepening_ways`] region wires FOUR of the crate's universes (keep, vault,
//!   bazaar, crypt) into a hub-and-branch map; the remaining two (hold, vaulted-bazaar) plug into
//!   the same registry once their winning scripts are added.
//! * Region turns are verified by chain-linkage + each cleared dungeon's full replay; a succinct
//!   region-level replay harness is a follow-up.

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, CellId, CellProgram, Effect, EmbeddedExecutor,
    FieldElement, StateConstraint, TransitionCase, TransitionGuard, TurnReceipt, field_from_u64,
    symbol,
};
use dregg_cell::{Cell, Permissions};
use spween::Scene;
use spween_dregg::{Driver, Playthrough, WorldCell, verify};

// ── The universe registry — a stable id → (deploy, scene, winning script) ─────────

/// **One playable universe on the map** — its stable id, display name, the real deploy + scene
/// constructors, and a canonical winning move-script (the choice indices that drive it START → WIN
/// through its real executor teeth, mirroring the crate's own `full_*_playthrough_reverifies`
/// tests). A [`Loc`] on the map references a universe by id.
#[derive(Clone)]
pub struct Universe {
    /// The universe's stable id (the key a [`Loc`] binds to).
    pub id: &'static str,
    /// The universe's display name.
    pub name: &'static str,
    /// Deploy a fresh real world-cell for this universe, deterministic in the seed.
    pub deploy: fn(u8) -> WorldCell,
    /// The parsed scene (the choices/conditions the moves are built from).
    pub scene: fn() -> Scene,
    /// The winning move-script — the choice indices that carry the universe to its WIN.
    pub win_script: fn() -> Vec<usize>,
}

/// The four wired universes, by id (the registry the map binds locations against). An unknown id is
/// `None` — a map referencing one is flagged by [`RegionMap::validate`].
pub fn universe(id: &str) -> Option<Universe> {
    let u = match id {
        "keep" => Universe {
            id: "keep",
            name: "The Warden's Keep",
            deploy: crate::deploy_keep,
            scene: crate::keep_scene,
            win_script: || {
                vec![
                    crate::KP_TRADE_BLOWS,
                    crate::KP_PRESS_ON,
                    crate::KP_CLAIM_RED,
                    crate::KP_DESCEND,
                    crate::KP_CAST_WARD,
                    crate::KP_SEIZE,
                ]
            },
        },
        "vault" => Universe {
            id: "vault",
            name: "The Sunken Vault",
            deploy: crate::deploy_vault,
            scene: crate::vault_scene,
            win_script: || {
                vec![
                    crate::VLT_CLAIM_GULL,
                    crate::VLT_TAKE_DRAUGHT,
                    crate::VLT_SWIM,
                    crate::VLT_TRADE_BLOW,
                    crate::VLT_DRINK,
                    crate::VLT_GRATE,
                    crate::VLT_SEIZE,
                ]
            },
        },
        "bazaar" => Universe {
            id: "bazaar",
            name: "The Ossuary Bazaar",
            deploy: crate::deploy_bazaar,
            scene: crate::bazaar_scene,
            win_script: || {
                vec![
                    crate::BAZ_ENTER,
                    crate::BAZ_BUY_POTION,
                    crate::BAZ_BUY_TORCHES,
                    crate::BAZ_TO_OSSUARY,
                    crate::BAZ_ROB_NICHE,
                    crate::BAZ_TRADE_BLOW,
                    crate::BAZ_DRINK,
                    crate::BAZ_LIGHT_TORCH,
                    crate::BAZ_CLIMB_BACK,
                    crate::BAZ_SELL_AMULET,
                    crate::BAZ_COUNTING_ROOM,
                    crate::BAZ_SEIZE,
                ]
            },
        },
        "crypt" => Universe {
            id: "crypt",
            name: "The Silent Crypt",
            deploy: crate::deploy_crypt,
            scene: crate::crypt_scene,
            win_script: || {
                vec![
                    crate::CRYPT_ENTER,
                    crate::NAVE_FORCE,
                    crate::NAVE_HUSH,
                    crate::NAVE_OPEN,
                    crate::CRYPT_SEIZE,
                ]
            },
        },
        _ => return None,
    };
    Some(u)
}

/// The outcome of driving a universe: the recorded [`Playthrough`], whether it reached a WIN (the
/// scene ended), and the universe id + seed it was played under (so [`reverify_win`] can re-deploy
/// the identical world-cell and replay it).
#[derive(Clone)]
pub struct WinRun {
    /// The universe id this run is for.
    pub id: String,
    /// The deterministic seed it was deployed under.
    pub seed: u8,
    /// The recorded playthrough (genesis + committed moves).
    pub playthrough: Playthrough,
    /// Whether the run reached a WIN (the scene ended).
    pub won: bool,
}

/// **Play a universe START → WIN** on a fresh identically-seeded real world-cell, returning the
/// recorded [`WinRun`]. Drives the universe's canonical winning script through the stock
/// [`Driver`]; every move is a real cap-bounded turn the executor admits. `won` is `true` iff the
/// scene ended. `None` for an unknown universe id.
pub fn play_to_win(id: &str, seed: u8) -> Option<WinRun> {
    let u = universe(id)?;
    Some(drive(&u, seed, (u.win_script)()))
}

/// **Play a universe only PARTWAY** — the first `moves` of its winning script — for the
/// non-vacuous "an unfinished run credits nothing" leg. The run does NOT reach a WIN (`won ==
/// false`), so the offering's completion gate refuses to clear it.
pub fn play_partial(id: &str, seed: u8, moves: usize) -> Option<WinRun> {
    let u = universe(id)?;
    let script: Vec<usize> = (u.win_script)().into_iter().take(moves).collect();
    Some(drive(&u, seed, script))
}

/// Drive `script` on a fresh `seed`-seeded deploy of `u`, recording the playthrough and whether the
/// scene ended. Each advance is a real executor turn; a script move the executor refuses panics
/// (the canonical winning script is a legal solving line, not a scripted win).
fn drive(u: &Universe, seed: u8, script: Vec<usize>) -> WinRun {
    let scene = (u.scene)();
    let mut driver = Driver::start((u.deploy)(seed), &scene)
        .unwrap_or_else(|e| panic!("universe `{}` starts: {e}", u.id));
    for (n, choice) in script.iter().enumerate() {
        driver.advance(*choice).unwrap_or_else(|e| {
            panic!("universe `{}` move {n} (choice {choice}) lands: {e}", u.id)
        });
    }
    WinRun {
        id: u.id.to_string(),
        seed,
        playthrough: driver.playthrough(),
        won: driver.is_ended(),
    }
}

/// **Re-verify a universe run by REPLAY** — re-deploy a fresh identically-seeded world-cell and
/// re-drive the recorded playthrough, confirming it reproduces exactly the committed state chain (a
/// forged / reordered / ineligible record fails). The SAME per-dungeon tooth each universe ships.
pub fn reverify_win(id: &str, seed: u8, play: &Playthrough) -> bool {
    let Some(u) = universe(id) else {
        return false;
    };
    verify((u.deploy)(seed), &(u.scene)(), play).is_ok()
}

// ── The region topology — locations joined by travel edges ────────────────────────

/// **A place on the region map — one universe.** Its stable `id` (the node id + the key in the
/// region cell's cleared flags), a display `name`, and the `universe_id` of the universe played
/// here ([`universe`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Loc {
    /// The location's stable id.
    pub id: String,
    /// The location's display name.
    pub name: String,
    /// The id of the universe played here ([`universe`]).
    pub universe_id: String,
}

impl Loc {
    /// A location builder.
    pub fn new(
        id: impl Into<String>,
        name: impl Into<String>,
        universe_id: impl Into<String>,
    ) -> Loc {
        Loc {
            id: id.into(),
            name: name.into(),
            universe_id: universe_id.into(),
        }
    }
}

/// **A directed travel road**, optionally `gate`d on COMPLETING a prerequisite location. While
/// `gate` is `Some(prereq)` and `prereq` is not yet cleared, the road is barred by the region
/// cell's `FieldGte(cleared[prereq], 1)` tooth. `None` is an always-open road.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RegionEdge {
    /// The location this road departs from.
    pub from: String,
    /// The location this road arrives at.
    pub to: String,
    /// The prerequisite location that must be cleared to travel this road, or `None`.
    pub gate: Option<String>,
}

impl RegionEdge {
    /// A road barred until `prereq` is cleared.
    pub fn gated(
        from: impl Into<String>,
        to: impl Into<String>,
        prereq: impl Into<String>,
    ) -> RegionEdge {
        RegionEdge {
            from: from.into(),
            to: to.into(),
            gate: Some(prereq.into()),
        }
    }
    /// An always-open road.
    pub fn open(from: impl Into<String>, to: impl Into<String>) -> RegionEdge {
        RegionEdge {
            from: from.into(),
            to: to.into(),
            gate: None,
        }
    }
}

/// **A named region — the connective world.** Locations (universes) joined by travel edges, opened
/// at `start`. Pure ruleset data; the live traversal is a [`RegionCell`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RegionMap {
    /// The region's stable id.
    pub id: String,
    /// The region's display name.
    pub name: String,
    /// The locations (universes) on the map.
    pub locations: Vec<Loc>,
    /// The travel roads between locations.
    pub edges: Vec<RegionEdge>,
    /// The starting location id.
    pub start: String,
}

impl RegionMap {
    /// The index of `loc` in [`Self::locations`], if present.
    pub fn index_of(&self, loc: &str) -> Option<usize> {
        self.locations.iter().position(|l| l.id == loc)
    }
    /// The location with `id`, if any.
    pub fn location(&self, id: &str) -> Option<&Loc> {
        self.locations.iter().find(|l| l.id == id)
    }
    /// Whether `id` names a known location.
    pub fn has_location(&self, id: &str) -> bool {
        self.locations.iter().any(|l| l.id == id)
    }
    /// The prerequisite that gates ENTERING `dest` (the gate of the first gated inbound edge), or
    /// `None` for an always-reachable destination. Each destination in a well-formed region carries
    /// at most one distinct gate (see [`deepening_ways`]).
    pub fn gate_of(&self, dest: &str) -> Option<String> {
        self.edges
            .iter()
            .filter(|e| e.to == dest)
            .find_map(|e| e.gate.clone())
    }
    /// The destinations reachable by a defined edge FROM `from`.
    pub fn edges_from(&self, from: &str) -> Vec<&RegionEdge> {
        self.edges.iter().filter(|e| e.from == from).collect()
    }
    /// **Well-formedness flaws** (empty = well-formed): every location's universe resolves, `start`
    /// and every edge endpoint + gate name a known location.
    pub fn validate(&self) -> Vec<String> {
        let mut flaws = Vec::new();
        for l in &self.locations {
            if universe(&l.universe_id).is_none() {
                flaws.push(format!(
                    "location `{}` references unknown universe `{}`",
                    l.id, l.universe_id
                ));
            }
        }
        if !self.has_location(&self.start) {
            flaws.push(format!("start `{}` is not a known location", self.start));
        }
        for e in &self.edges {
            if !self.has_location(&e.from) {
                flaws.push(format!(
                    "edge {}->{} from unknown `{}`",
                    e.from, e.to, e.from
                ));
            }
            if !self.has_location(&e.to) {
                flaws.push(format!("edge {}->{} to unknown `{}`", e.from, e.to, e.to));
            }
            if let Some(g) = &e.gate {
                if !self.has_location(g) {
                    flaws.push(format!(
                        "edge {}->{} gated on unknown `{}`",
                        e.from, e.to, g
                    ));
                }
            }
        }
        flaws
    }
    /// Whether the region validates cleanly.
    pub fn is_well_formed(&self) -> bool {
        self.validate().is_empty()
    }
}

/// **THE DEEPENING WAYS — the concrete region wiring four universes into one hub-and-branch map.**
/// The Keep is the hub (START); clearing it opens the two mid dungeons (the Vault and the Bazaar);
/// clearing the Vault opens the way down to the Silent Crypt, the deep end. So the map opens as you
/// honestly clear its dungeons:
///
/// ```text
///   keep  (START, the hub)
///     ├─ gated on keep ──▶ vault ─ gated on vault ─▶ crypt  (the deep end)
///     └─ gated on keep ──▶ bazaar                    (a side branch)
/// ```
///
/// Open return roads (backtrack) let a traveller walk home freely; only the FORWARD roads into the
/// deeper dungeons are verified-completion-gated. (A destination with both a gated and an open
/// inbound road keeps its gate — [`RegionMap::gate_of`] finds the gated one — so revisiting the
/// vault still requires the keep cleared.)
pub fn deepening_ways() -> RegionMap {
    RegionMap {
        id: "deepening-ways".into(),
        name: "The Deepening Ways".into(),
        locations: vec![
            Loc::new("keep", "The Warden's Keep", "keep"),
            Loc::new("vault", "The Sunken Vault", "vault"),
            Loc::new("bazaar", "The Ossuary Bazaar", "bazaar"),
            Loc::new("crypt", "The Silent Crypt", "crypt"),
        ],
        edges: vec![
            // The forward, verified-completion-gated roads (the load-bearing ones).
            RegionEdge::gated("keep", "vault", "keep"),
            RegionEdge::gated("keep", "bazaar", "keep"),
            RegionEdge::gated("vault", "crypt", "vault"),
            // Open return roads (walk home freely).
            RegionEdge::open("vault", "keep"),
            RegionEdge::open("bazaar", "keep"),
            RegionEdge::open("crypt", "vault"),
        ],
        start: "keep".into(),
    }
}

// ── The region cell — the map as a real dregg cell on a real executor ─────────────

/// A fixed federation id the region's turns commit under (a demo federation).
const FEDERATION: [u8; 32] = [0x0E; 32];
/// A fixed driver seed so the region cell's driver identity is stable per deploy.
const DRIVER_SEED: [u8; 64] = [0x2E; 64];
/// The state slot holding the `current_location` marker (the traveller's position).
const CURRENT_SLOT: u8 = 0;

/// The `cleared` flag slot for the location at index `i` (slots `1..=N`, past `current`).
fn cleared_slot(i: usize) -> u8 {
    (1 + i) as u8
}
/// The sanctioned method that clears location `loc`.
fn clear_method(loc: &str) -> String {
    format!("overworld/clear/{loc}")
}
/// The method that travels to destination `dest`.
fn travel_method(loc: &str) -> String {
    format!("overworld/travel/{loc}")
}
/// A NON-sanctioned method (never installed as a case) — the forged path a cheat would try.
fn forge_method(loc: &str) -> String {
    format!("overworld/forge/{loc}")
}

/// A cell whose permissions gate nothing (the gate + WriteOnce teeth are the load-bearing ones, as
/// in [`crate::multicell`]).
fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

/// **The live traversal of a region — a real dregg cell on a real executor.** Holds the shared
/// executor ledger, the region cell (its `current_location` + per-location WriteOnce cleared flags),
/// and the installed [`CellProgram::Cases`] program (the travel-gate + clear teeth). Travel and
/// clear are real cap-bounded turns the verified executor admits or refuses.
pub struct RegionCell {
    exec: EmbeddedExecutor,
    cclerk: AppCipherclerk,
    cell: CellId,
    map: RegionMap,
}

impl RegionCell {
    /// **Deploy the region as a real world cell** — build the cell with the map's travel-gate +
    /// clear cases installed, insert it on a fresh executor, and grant the driver a cap to it.
    /// Deterministic in `seed`.
    pub fn deploy(map: &RegionMap, seed: u8) -> RegionCell {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::from_seed(DRIVER_SEED), FEDERATION);
        let exec = EmbeddedExecutor::new(&cclerk, "default");
        let driver = cclerk.cell_id();

        // Build the CellProgram: a clear case per location (WriteOnce on its cleared flag) and a
        // travel case per location (FieldGte on its prerequisite's cleared flag, or unconstrained).
        let mut cases: Vec<TransitionCase> = Vec::new();
        for (i, loc) in map.locations.iter().enumerate() {
            cases.push(TransitionCase {
                guard: TransitionGuard::MethodIs {
                    method: symbol(&clear_method(&loc.id)),
                },
                constraints: vec![StateConstraint::WriteOnce {
                    index: cleared_slot(i),
                }],
            });
        }
        for loc in &map.locations {
            let constraints = match map.gate_of(&loc.id) {
                Some(prereq) => {
                    let pi = map.index_of(&prereq).expect("gate names a known location");
                    vec![StateConstraint::FieldGte {
                        index: cleared_slot(pi),
                        value: field_from_u64(1),
                    }]
                }
                None => Vec::new(),
            };
            cases.push(TransitionCase {
                guard: TransitionGuard::MethodIs {
                    method: symbol(&travel_method(&loc.id)),
                },
                constraints,
            });
        }

        let mut pk = [0u8; 32];
        pk[0] = seed;
        pk[31] = seed.wrapping_mul(41);
        let mut cell = Cell::with_balance(pk, [0u8; 32], 0);
        cell.permissions = open_permissions();
        cell.program = CellProgram::Cases(cases);
        let cell_id = cell.id();

        exec.ensure_cell(cell).expect("region cell inserts");
        exec.with_ledger_mut(|ledger| {
            if let Some(agent) = ledger.get_mut(&driver) {
                agent.capabilities.grant(cell_id, AuthRequired::None);
            }
        });

        RegionCell {
            exec,
            cclerk,
            cell: cell_id,
            map: map.clone(),
        }
    }

    /// The region topology this cell holds.
    pub fn map(&self) -> &RegionMap {
        &self.map
    }
    /// The region cell's id.
    pub fn cell_id(&self) -> CellId {
        self.cell
    }

    /// Read cell slot `slot` from the committed ledger.
    fn read(&self, slot: usize) -> FieldElement {
        self.exec
            .cell_state(self.cell)
            .map(|s| s.fields[slot])
            .unwrap_or([0u8; 32])
    }

    /// Whether location `loc` is cleared (its WriteOnce flag is set).
    pub fn is_cleared(&self, loc: &str) -> bool {
        match self.map.index_of(loc) {
            Some(i) => self.read(cleared_slot(i) as usize) != field_from_u64(0),
            None => false,
        }
    }
    /// How many locations are cleared.
    pub fn cleared_count(&self) -> usize {
        (0..self.map.locations.len())
            .filter(|&i| self.read(cleared_slot(i) as usize) != field_from_u64(0))
            .count()
    }
    /// The location the traveller currently stands in (the committed `current_location` marker).
    pub fn current_location(&self) -> String {
        let cur = self.read(CURRENT_SLOT as usize);
        for (i, loc) in self.map.locations.iter().enumerate() {
            if cur == field_from_u64(i as u64) {
                return loc.id.clone();
            }
        }
        self.map.start.clone()
    }

    /// Issue one real cap-bounded turn (build → sign → wrap → submit) — the executor admits it IFF
    /// the driver's cap AND the touched cell's program admit it. Returns the receipt or the
    /// refusal reason.
    fn issue(&self, method: &str, effects: Vec<Effect>) -> Result<TurnReceipt, String> {
        let action = self.cclerk.make_action(self.cell, method, effects);
        let action = self.cclerk.sign_action(action);
        let turn = self.cclerk.make_turn(action);
        self.exec.submit_turn(&turn).map_err(|e| e.to_string())
    }

    /// **Clear location `loc` — the sanctioned completion turn.** Sets its WriteOnce cleared flag on
    /// a real committed turn. The offering fires this ONLY after a genuine, replay-verified WIN of
    /// the location's universe (the session-level binding). A first clear (0→1) commits; a re-clear
    /// is idempotent. Refused if `loc` is unknown.
    pub fn clear(&self, loc: &str) -> Result<TurnReceipt, String> {
        let i = self
            .map
            .index_of(loc)
            .ok_or_else(|| format!("`{loc}` is not a place in this region"))?;
        self.issue(
            &clear_method(loc),
            vec![Effect::SetField {
                cell: self.cell,
                index: cleared_slot(i) as u64,
                value: field_from_u64(1),
            }],
        )
    }

    /// **Travel to `dest` — the gated travel turn.** Writes the `current_location` marker; the
    /// executor admits it IFF `cleared[prereq(dest)] >= 1` (a real `FieldGte` tooth). Before the
    /// prerequisite is cleared this is a real executor REFUSAL that commits nothing. Refused if
    /// `dest` is unknown or has no defined travel case.
    pub fn travel(&self, dest: &str) -> Result<TurnReceipt, String> {
        let di = self
            .map
            .index_of(dest)
            .ok_or_else(|| format!("`{dest}` is not a place in this region"))?;
        self.issue(
            &travel_method(dest),
            vec![Effect::SetField {
                cell: self.cell,
                index: CURRENT_SLOT as u64,
                value: field_from_u64(di as u64),
            }],
        )
    }

    /// **A FORGED clear — writing a cleared flag under a NON-sanctioned method.** The `Cases`
    /// program is default-deny: no case matches this method, so the executor REFUSES it
    /// (`NoTransitionCaseMatched`) — a cleared flag cannot be minted outside the sanctioned `clear`
    /// path. The non-vacuous contrast to [`Self::clear`], driven in the forged-flag test.
    pub fn forge_cleared(&self, loc: &str) -> Result<TurnReceipt, String> {
        let i = self
            .map
            .index_of(loc)
            .ok_or_else(|| format!("`{loc}` is not a place in this region"))?;
        self.issue(
            &forge_method(loc),
            vec![Effect::SetField {
                cell: self.cell,
                index: cleared_slot(i) as u64,
                value: field_from_u64(1),
            }],
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_deepening_ways_is_well_formed() {
        let map = deepening_ways();
        assert!(
            map.is_well_formed(),
            "concrete region validates: {:?}",
            map.validate()
        );
        assert_eq!(map.locations.len(), 4, "four universes wired");
        assert_eq!(map.gate_of("vault").as_deref(), Some("keep"));
        assert_eq!(map.gate_of("crypt").as_deref(), Some("vault"));
    }

    #[test]
    fn validate_flags_an_unknown_universe_and_a_dangling_edge() {
        let map = RegionMap {
            id: "broken".into(),
            name: "Broken".into(),
            locations: vec![
                Loc::new("a", "A", "keep"),
                Loc::new("b", "B", "not-a-universe"),
            ],
            edges: vec![RegionEdge::open("a", "nowhere")],
            start: "a".into(),
        };
        let flaws = map.validate();
        assert!(
            flaws.iter().any(|f| f.contains("not-a-universe")),
            "{flaws:?}"
        );
        assert!(flaws.iter().any(|f| f.contains("nowhere")), "{flaws:?}");
        assert!(!map.is_well_formed());
    }

    #[test]
    fn each_wired_universe_plays_to_a_verified_win() {
        for id in ["keep", "vault", "bazaar", "crypt"] {
            let run = play_to_win(id, 40).expect("known universe");
            assert!(run.won, "universe `{id}` reaches a WIN");
            assert!(
                reverify_win(id, run.seed, &run.playthrough),
                "universe `{id}` replays"
            );
        }
    }

    /// THE HARD GATE, refusal + commit legs, on the real executor. Travel to the vault is REFUSED
    /// before the keep is cleared; a FORGED clear (non-sanctioned method) is REFUSED; the sanctioned
    /// clear commits and the SAME travel then commits (non-vacuous).
    #[test]
    fn travel_is_gated_on_verified_completion_and_the_gate_opens() {
        let map = deepening_ways();
        let region = RegionCell::deploy(&map, 7);
        assert_eq!(region.current_location(), "keep");
        assert!(!region.is_cleared("keep"));

        // Locked: the road to the vault is barred until the keep is cleared.
        let locked = region.travel("vault");
        assert!(
            locked.is_err(),
            "travel to a locked dungeon is refused, got {locked:?}"
        );
        assert_eq!(region.cleared_count(), 0, "anti-ghost: nothing cleared");

        // Forged: a cleared flag written under a non-sanctioned method fails closed.
        let forged = region.forge_cleared("keep");
        assert!(
            forged.is_err(),
            "a forged cleared flag is refused, got {forged:?}"
        );
        assert!(
            !region.is_cleared("keep"),
            "anti-ghost: keep still not cleared"
        );

        // Clear the keep the sanctioned way (a real committed turn) — the gate OPENS.
        region.clear("keep").expect("the sanctioned clear commits");
        assert!(region.is_cleared("keep"));

        // The SAME travel now commits (non-vacuous).
        region
            .travel("vault")
            .expect("the gate to the vault is open now");
        assert_eq!(region.current_location(), "vault");

        // The deeper road stays sealed until the vault is cleared.
        let deep_locked = region.travel("crypt");
        assert!(
            deep_locked.is_err(),
            "the crypt stays sealed until the vault is cleared, got {deep_locked:?}"
        );
        region.clear("vault").expect("clear the vault");
        region
            .travel("crypt")
            .expect("clearing the vault opens the way to the crypt");
        assert_eq!(region.current_location(), "crypt");
        assert_eq!(region.cleared_count(), 2);
    }
}
