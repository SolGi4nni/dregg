//! # The Descent, reimagined — LEAN-AUTHORED rules on the real executor.
//!
//! This is the flagship descent rebuilt as the dreggic object it wants to be, and its
//! rules are **not written in Rust at all**. The game — its design laws AND its deployed
//! `CellProgram` teeth — is authored in Lean:
//!
//! * `metatheory/Dregg2/Games/Dungeon.lean` — the reimagined game (relics as owned
//!   objects with a custody RATCHET, provenance to the mint; descent ATTENUATES carrying
//!   rights `pack + depth ≤ CAP`; the light is the clock, permadeath is a theorem; keys
//!   are exercised capabilities; banking is terminal), each law machine-checked.
//! * `metatheory/Dregg2/Games/DungeonProgram.lean :: dungeonProgram` — the deployed
//!   teeth as a Lean value over the LAW-#1 `Exec` algebra, with admission-soundness
//!   theorems over arbitrary states and a driven crowned-run/attack `#guard` battery.
//!
//! The value is emitted to the checked-in artifact [`PROGRAM_JSON`]
//! (`program/dungeon_program.json`, regenerate-and-diff gated by `program/regen.sh`)
//! and THIS module does the only Rust-side work: deserialize the symbolic artifact and
//! resolve names against the translation-validated `dregg-schema` allocator
//! ([`Deployment`]). There is NO hand-rolled `CellProgram` in the descent's path — the
//! deployed program IS the Lean object by construction (edit a rule in the Lean source,
//! re-emit via `program/regen.sh`, and the deployed game changes: the canary).
//!
//! ## What the emitted program carries (beyond the tug pattern)
//!
//! The artifact authors GUARDS, not just method cases: `slotChangedForMethods` riders
//! lower to `AllOf[SlotChanged, AnyOf[MethodIs…]]`, so ANY verb that moves `depth` pays
//! the delve law, ANY verb that flips a `way_w` must EXHIBIT the carried key-relic
//! (`HeapField{Equals CARRIED}` — the key is an owned capability, exercised, receipted),
//! ANY `bank`/`fate` move is a lawful banking, and ANY exertion pays the
//! conservation/ratchet/capacity commons. This retires the stapleable-slot hole class
//! structurally while keeping the executor's method-default-deny (the method disjunct
//! inside the rider guard).
//!
//! ## Two blows: the press and the LUNGE (the guardian breaks your grip)
//!
//! The Descent has no hit points to take, so the guardian's counter-blow is priced in the
//! only currency the run has: CAPACITY. `harm` is a run-long `0..=HARMCAP` ratchet and the
//! capacity law is `pack + depth + harm <= CAP` — every point of harm is one relic that
//! does not leave the dungeon. Two verbs land the same wound:
//!
//! * [`SMITE`] — the press: 2 breath, no harm (byte-identical to what the descent shipped);
//! * [`LUNGE`] — 1 breath and `harm += 1`. Save a breath, pay a carry slot.
//!
//! It is a real decision because capacity already attenuates with depth: the same posted
//! price is cheap at depth 1 (7 slots) and ruinous at depth 4 (4 slots — exactly three keys
//! plus the prize). Lean states the stake as law: `Dungeon.crowned_full_bank_harmless` — a
//! run that banks the prize AND all three keys took NO harm at all. Unlike `wounds`, `harm`
//! is NOT reset by [`Sim::delve`] (`Dungeon.harm_ratchets`).
//!
//! ## The map is DAILY — drawn from the committed day-seed
//!
//! The descent used to ship one compile-time map: the same eight mint floors and the same
//! four guardians every day, so a solved line replayed forever. It no longer does. The
//! Lean model takes the world as a parameter (`Dungeon.WorldParam` — where each relic is
//! minted and how tough each floor's guardian is), and `Dungeon.drawFamily` is the family
//! of [`DAYS`] maps the committed drand day-seed draws from ([`day_index`]).
//!
//! Every drawn map is CHECKED and DRIVEN in Lean, not hoped:
//!
//! * `Dungeon.drawFamily_wf` — each map is structurally legal: relic 0 (THE PRIZE) lies
//!   at the bottom, and **no key is ever minted behind the door it opens**
//!   (`homes (keyFor w) < w`), so every way is openable from the surface;
//! * `Dungeon.winsAt_true` / `Dungeon.draw_completable` — for each map, the crowned line
//!   GENERATED from that map replays legally through the real rulebook and banks the
//!   prize. Completability is a witness, not an assumption;
//! * `Dungeon.costAt_tense` — every day's perfect line costs 20–26 of the 26 breath, and
//!   capacity stays exactly as tight as the shipped map's (`pack + depth ≤ CAP` means the
//!   bottom holds three keys plus the prize and nothing else);
//! * `DungeonProgram.crownedRunAdmitted` — each day's crowned line is admitted end to end
//!   by the teeth emitted for THAT day.
//!
//! [`PROGRAM_JSON`] therefore carries the whole family: one fully emitted 15-case program
//! per map. Rust picks the index and resolves names to slots — it never assembles or
//! edits a constraint. [`Descent::deploy_on_day`] is the daily entry (the beacon draws the
//! map); [`Descent::deploy`] pins day 0, the shipped map, so a fixed script stays a fixed
//! dungeon for tests and replays.
//!
//! ## The mover vs. the referee
//!
//! [`Sim`] is the ENGINE (the mover): it computes the next projection off-circuit, in
//! the portfolio's translation-validation shape. The REFEREE is the installed
//! Lean-sourced program — the executor re-checks every committed post-state against the
//! teeth, and a forged projection (dupe a relic, flip a way keylessly, move after
//! banking…) is a real [`WorldError::Refused`], driven in
//! `tests/descent_lean_sourced.rs`.

use std::collections::BTreeMap;
use std::sync::Arc;

use dregg_app_framework::{
    CellId, CellProgram, Effect, Event, StateConstraint, TransitionCase, TransitionGuard,
    TurnReceipt, field_from_u64, symbol,
};
use dregg_cell::program::{HeapAtom, SimpleStateConstraint};
use dregg_schema::layout::{CheckedLayout, Slot, allocate_checked};
use dregg_schema::schema::Schema;
use procgen_dregg::CommittedSeed;
use serde::Deserialize;
use spween_dregg::{CompiledStory, GENESIS_DONE_EXT_KEY, WorldCell, WorldError};

use crate::loot::{LootError, LootItem, LootVault, banked_relic_drop};

/// The scene id that fixes the deterministic world-cell identity (must match the Lean
/// emit's `Dregg2.Games.Dungeon.Prog.sceneId`).
pub const SCENE_ID: &str = "dungeon-on-dregg/descent1";

/// The one-shot mint (spween's genesis method name — the world births + writes the
/// genesis-done sentinel for it because the LOADED program's genesis case carries the
/// sentinel teeth).
pub const GENESIS: &str = "genesis";
pub const DELVE: &str = "delve";
pub const UNLOCK: &str = "unlock";
/// **The press** — wound the guardian for 2 breath and no harm.
pub const SMITE: &str = "smite";
/// **The lunge** — the same wound for 1 breath, paid with `+1 harm` (a carry slot).
pub const LUNGE: &str = "lunge";
pub const LOOT: &str = "loot";
pub const FLEE: &str = "flee";

/// The world constants — the Lean model's (`Dregg2.Games.Dungeon`); the DEPLOYED
/// copies of these numbers live in the emitted artifact, not here. These exist so the
/// Rust mover can compute projections; the referee is the loaded program.
pub const FLOORS: u64 = 4;
pub const RELICS: usize = 8;
pub const BREATH: u64 = 26;
pub const CAP: u64 = 8;
pub const CARRIED: u64 = 8;
pub const BANKED: u64 = 9;
/// The most harm a run can take: `harm` is a run-long `0..=2` ratchet, and every point
/// of it is a permanently forfeited carry slot (`pack + depth + harm <= CAP`).
/// The Lean `Dregg2.Games.Dungeon.HARMCAP`.
pub const HARMCAP: u64 = 2;
/// **The number of distinct maps the committed day-seed draws from** (the Lean
/// `Dregg2.Games.Dungeon.dayCount`). Every member is checked legal and DRIVEN to a win in
/// Lean (`drawFamily_wf`, `winsAt_true`), and every member has its own fully emitted
/// 15-case program in [`PROGRAM_JSON`].
pub const DAYS: usize = 16;

/// Day 0 — the shipped map, kept as the canonical/default world. Relic 0 = THE PRIZE
/// (floor 4); relics 1–3 = the keys to ways 2–4; relics 4–7 = treasures.
/// (The Lean `drawFamily[0]`.)
pub const HOME: [u64; RELICS] = [4, 1, 2, 3, 1, 1, 2, 3];

/// **The day's map, read out of the Lean-emitted artifact.** The mint homes and the
/// per-floor guardian vitalities are NOT constants any more: they are drawn from the
/// committed day-seed, and the deployed teeth for that draw are the ones the loader
/// installs. Rust reads the numbers Lean emitted; it never picks them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DayWorld {
    /// Per-relic minted floor (the Lean `World.homes`).
    pub homes: [u64; RELICS],
    /// Per-floor guardian vitality, index 0 = the surface (the Lean `World.ghp`).
    pub ghp: [u64; FLOORS as usize + 1],
}

impl DayWorld {
    /// Floor `depth`'s guardian vitality (the Lean `guardHp`).
    pub fn guard_hp(&self, depth: u64) -> u64 {
        self.ghp.get(depth as usize).copied().unwrap_or(0)
    }
}

/// Day 0's world (the shipped map).
pub const CANON_WORLD: DayWorld = DayWorld {
    homes: HOME,
    ghp: [0, 1, 1, 2, 2],
};

/// **The day's world for family index `day`** — parsed from the Lean-emitted artifact so
/// the mover and the installed teeth cannot describe different dungeons. Out-of-range
/// indices fold to day 0, exactly as the Lean `worldAt` does.
pub fn day_world(day: usize) -> DayWorld {
    let sym = family();
    match sym.worlds.iter().find(|w| w.day == day) {
        Some(w) => DayWorld {
            homes: w.homes.as_slice().try_into().expect("8 minted relic homes"),
            ghp: w
                .ghp
                .as_slice()
                .try_into()
                .expect("FLOORS+1 guardian vitalities"),
        },
        None => CANON_WORLD,
    }
}

/// Reduce a committed day-seed to a family index. This is the ONLY place the beacon
/// touches the map: everything downstream is a total function of the index, and every
/// index in range is a Lean-checked, Lean-driven-completable dungeon.
pub fn day_index(day_seed: &CommittedSeed) -> usize {
    let bytes = day_seed.as_bytes();
    let mut acc = [0u8; 8];
    acc.copy_from_slice(&bytes[..8]);
    (u64::from_le_bytes(acc) % DAYS as u64) as usize
}

/// Per-floor guardian vitality on DAY 0 (the shipped map's Lean `guardHp`). Day-varying
/// callers use [`DayWorld::guard_hp`] / [`Sim::guard_hp`].
pub fn guard_hp(depth: u64) -> u64 {
    CANON_WORLD.guard_hp(depth)
}

/// The 14 register components, in allocation order.  The six custody
/// projections occupy fields 0..6 contiguously so the custom recursion fold
/// can weld the AIR-counted census to the exact post-state registers in one
/// mandatory app-root binding.  This is a greenfield layout epoch; all game
/// logic resolves names through [`Deployment::reg`] and does not hard-code the
/// former numeric order.
///
/// ⚑ `harm` is APPENDED last: register slots are assigned in declaration order, so the
/// thirteen that were here keep their slots and the custody-projection prefix is
/// untouched.
pub const REGISTERS: [&str; 14] = [
    "pack", "bank", "hoard_1", "hoard_2", "hoard_3", "hoard_4", "depth", "spent", "wounds", "fate",
    "way_2", "way_3", "way_4", "harm",
];

pub fn relic_name(i: usize) -> String {
    format!("relic_{i}")
}

/// Build the declared schema: 14 register components + 8 relic-custody collections.
pub fn schema() -> Schema {
    let mut s = Schema::new(SCENE_ID)
        .stat("pack", 0, RELICS as u64)
        .stat("bank", 0, RELICS as u64)
        // A drawn map may pile several relics on one floor, so each hoard carries the
        // whole conservation range (the Lean `rangeTeeth` says exactly `[0, RELICS]`).
        // Register slots are assigned in DECLARATION order, so widening the ranges does
        // not move any slot.
        .stat("hoard_1", 0, RELICS as u64)
        .stat("hoard_2", 0, RELICS as u64)
        .stat("hoard_3", 0, RELICS as u64)
        .stat("hoard_4", 0, RELICS as u64)
        .stat("depth", 0, FLOORS)
        .stat("spent", 0, BREATH)
        .stat("wounds", 0, 2)
        .stat("fate", 0, 1)
        .stat("way_2", 0, 1)
        .stat("way_3", 0, 1)
        .stat("way_4", 0, 1)
        // The run-long grip ratchet. Declared LAST so no existing slot moves; its range
        // is the Lean `HARMCAP` and the emitted `inRangeTwoSided harm 0 2` tooth.
        .stat("harm", 0, HARMCAP);
    for i in 0..RELICS {
        s = s.collection(relic_name(i));
    }
    s
}

/// The consumed, Legal-checked layout + the Lean-loaded teeth for ONE day's map.
pub struct Deployment {
    pub layout: CheckedLayout,
    /// Which map of the drawn family this deployment installs the teeth for.
    pub day: usize,
}

impl Deployment {
    /// Day 0 — the shipped map.
    pub fn new() -> Self {
        Self::for_day(0)
    }

    /// The deployment for family index `day` (the committed day-seed picks it via
    /// [`day_index`]). The layout is identical across days — only the teeth differ.
    pub fn for_day(day: usize) -> Self {
        let layout = allocate_checked(&schema()).expect("descent layout is Legal");
        Deployment {
            layout,
            day: day % DAYS,
        }
    }

    /// The day's map (mint homes + guardian vitalities), read from the Lean artifact.
    pub fn world(&self) -> DayWorld {
        day_world(self.day)
    }

    /// Resolve a register component to its slot index.
    pub fn reg(&self, name: &str) -> u8 {
        match self.layout.resolve(name) {
            Some(Slot::Register(r)) => r,
            other => panic!("`{name}` is not a register: {other:?}"),
        }
    }

    /// Resolve a heap component to its key.
    pub fn key(&self, name: &str) -> u64 {
        match self.layout.resolve(name) {
            Some(Slot::Heap(k)) => k,
            other => panic!("`{name}` is not a heap key: {other:?}"),
        }
    }

    pub fn relic_key(&self, i: usize) -> u64 {
        self.key(&relic_name(i))
    }

    /// The descent teeth for THIS deployment's day, **LOADED from the Lean source of
    /// truth** — see [`load_program_for_day`]. No hand-rolled `CellProgram` exists in
    /// this crate for the descent; the deployed program IS the Lean object, emitted once
    /// per drawn map.
    pub fn program(&self) -> CellProgram {
        load_program_for_day(self, self.day)
    }

    /// The compiled story to install on the world-cell.
    pub fn story(&self) -> CompiledStory {
        let mut var_slots = BTreeMap::new();
        for name in REGISTERS {
            var_slots.insert(name.to_string(), self.reg(name) as u64);
        }
        CompiledStory {
            scene_id: SCENE_ID.to_string(),
            var_slots,
            has_slots: BTreeMap::new(),
            passage_index: BTreeMap::new(),
            program: self.program(),
            fully_gated: BTreeMap::new(),
        }
    }
}

impl Default for Deployment {
    fn default() -> Self {
        Self::new()
    }
}

// =============================================================================
// The Lean-artifact loader (the ONLY Rust-side work in the descent's rule path).
// =============================================================================

/// The checked-in Lean-emitted artifact (a CACHE of the verified Lean emission;
/// Lean is the source of truth, regenerated by `program/regen.sh`).
pub const PROGRAM_JSON: &str = include_str!("../program/dungeon_program.json");

/// The Lean-emitted artifact: the scene, the family size, and one FULLY emitted program
/// per drawn map. Rust picks an index and resolves symbolic names to slots; it neither
/// authors nor assembles a constraint.
#[derive(Debug, Deserialize)]
struct SymProgram {
    scene: String,
    days: usize,
    worlds: Vec<SymWorld>,
}

/// One day of the drawn family: the map itself (so the mover reads the same numbers the
/// teeth were emitted from) plus that day's complete case list.
#[derive(Debug, Deserialize)]
struct SymWorld {
    day: usize,
    homes: Vec<u64>,
    ghp: Vec<u64>,
    cases: Vec<SymCase>,
}

#[derive(Debug, Deserialize)]
struct SymCase {
    guard: SymGuard,
    constraints: Vec<SymConstraint>,
}

/// Mirrors Lean `Guard` — the descent authors guards, not just method names.
#[derive(Debug, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase")]
enum SymGuard {
    MethodIs { method: String },
    SlotChangedForMethods { reg: String, methods: Vec<String> },
}

/// Mirrors Lean `Constraint` (the descent's `StateConstraint` subset).
#[derive(Debug, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase")]
enum SymConstraint {
    FieldEquals {
        reg: String,
        value: u64,
    },
    FieldGte {
        reg: String,
        value: u64,
    },
    FieldLte {
        reg: String,
        value: u64,
    },
    FieldDelta {
        reg: String,
        d: u64,
    },
    StrictMonotonic {
        reg: String,
    },
    Immutable {
        reg: String,
    },
    SumEquals {
        regs: Vec<String>,
        value: u64,
    },
    AffineLe {
        terms: Vec<(i64, String)>,
        c: i64,
    },
    InRangeTwoSided {
        reg: String,
        lo: u64,
        hi: u64,
    },
    AllowedTransitions {
        reg: String,
        allowed: Vec<(u64, u64)>,
    },
    AnyOf {
        variants: Vec<SymSimple>,
    },
    HeapField {
        key: SymKey,
        atom: SymAtom,
    },
    /// Exact fixed-key aggregate authored by Lean: the number of resolved
    /// post-state keys equal to `value` must equal the named register.
    CountFieldsEq {
        keys: Vec<SymKey>,
        value: u64,
        reg: String,
    },
}

/// Mirrors Lean `Simple` (the anyOf-liftable subset).
#[derive(Debug, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase")]
enum SymSimple {
    FieldEquals { reg: String, value: u64 },
    FieldGte { reg: String, value: u64 },
    FieldLte { reg: String, value: u64 },
    Immutable { reg: String },
    Not { inner: Box<SymSimple> },
}

/// Mirrors Lean `HeapKeyRef`.
#[derive(Debug, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase")]
enum SymKey {
    Named { name: String },
    Sentinel,
}

/// Mirrors Lean `HeapAtom` (the descent's subset).
#[derive(Debug, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase")]
enum SymAtom {
    Equals { value: u64 },
    Immutable,
    Monotonic,
    MemberOf { set: Vec<u64> },
    DeltaEquals { d: i64 },
}

impl SymGuard {
    fn resolve(&self, dep: &Deployment) -> TransitionGuard {
        match self {
            SymGuard::MethodIs { method } => TransitionGuard::MethodIs {
                method: symbol(method),
            },
            SymGuard::SlotChangedForMethods { reg, methods } => TransitionGuard::AllOf(vec![
                TransitionGuard::SlotChanged {
                    index: dep.reg(reg),
                },
                TransitionGuard::AnyOf(
                    methods
                        .iter()
                        .map(|m| TransitionGuard::MethodIs { method: symbol(m) })
                        .collect(),
                ),
            ]),
        }
    }
}

impl SymKey {
    fn resolve(&self, dep: &Deployment) -> u64 {
        match self {
            SymKey::Named { name } => dep.key(name),
            SymKey::Sentinel => GENESIS_DONE_EXT_KEY,
        }
    }
}

impl SymAtom {
    fn resolve(&self) -> HeapAtom {
        match self {
            SymAtom::Equals { value } => HeapAtom::Equals {
                value: field_from_u64(*value),
            },
            SymAtom::Immutable => HeapAtom::Immutable,
            SymAtom::Monotonic => HeapAtom::Monotonic,
            SymAtom::MemberOf { set } => HeapAtom::MemberOf { set: set.clone() },
            SymAtom::DeltaEquals { d } => HeapAtom::DeltaEquals { d: *d },
        }
    }
}

impl SymSimple {
    fn resolve(&self, dep: &Deployment) -> SimpleStateConstraint {
        match self {
            SymSimple::FieldEquals { reg, value } => SimpleStateConstraint::FieldEquals {
                index: dep.reg(reg),
                value: field_from_u64(*value),
            },
            SymSimple::FieldGte { reg, value } => SimpleStateConstraint::FieldGte {
                index: dep.reg(reg),
                value: field_from_u64(*value),
            },
            SymSimple::FieldLte { reg, value } => SimpleStateConstraint::FieldLte {
                index: dep.reg(reg),
                value: field_from_u64(*value),
            },
            SymSimple::Immutable { reg } => SimpleStateConstraint::Immutable {
                index: dep.reg(reg),
            },
            SymSimple::Not { inner } => SimpleStateConstraint::Not(Box::new(inner.resolve(dep))),
        }
    }
}

impl SymConstraint {
    fn resolve(&self, dep: &Deployment) -> StateConstraint {
        match self {
            SymConstraint::FieldEquals { reg, value } => StateConstraint::FieldEquals {
                index: dep.reg(reg),
                value: field_from_u64(*value),
            },
            SymConstraint::FieldGte { reg, value } => StateConstraint::FieldGte {
                index: dep.reg(reg),
                value: field_from_u64(*value),
            },
            SymConstraint::FieldLte { reg, value } => StateConstraint::FieldLte {
                index: dep.reg(reg),
                value: field_from_u64(*value),
            },
            SymConstraint::FieldDelta { reg, d } => StateConstraint::FieldDelta {
                index: dep.reg(reg),
                delta: field_from_u64(*d),
            },
            SymConstraint::StrictMonotonic { reg } => StateConstraint::StrictMonotonic {
                index: dep.reg(reg),
            },
            SymConstraint::Immutable { reg } => StateConstraint::Immutable {
                index: dep.reg(reg),
            },
            SymConstraint::SumEquals { regs, value } => StateConstraint::SumEquals {
                indices: regs.iter().map(|n| dep.reg(n)).collect(),
                value: field_from_u64(*value),
            },
            SymConstraint::AffineLe { terms, c } => StateConstraint::AffineLe {
                terms: terms.iter().map(|(k, n)| (*k, dep.reg(n))).collect(),
                c: *c,
            },
            SymConstraint::InRangeTwoSided { reg, lo, hi } => StateConstraint::InRangeTwoSided {
                index: dep.reg(reg),
                lo: *lo,
                hi: *hi,
            },
            SymConstraint::AllowedTransitions { reg, allowed } => {
                StateConstraint::AllowedTransitions {
                    slot_index: dep.reg(reg),
                    allowed: allowed
                        .iter()
                        .map(|(a, b)| (field_from_u64(*a), field_from_u64(*b)))
                        .collect(),
                }
            }
            SymConstraint::AnyOf { variants } => StateConstraint::AnyOf {
                variants: variants.iter().map(|v| v.resolve(dep)).collect(),
            },
            SymConstraint::HeapField { key, atom } => StateConstraint::HeapField {
                key: key.resolve(dep),
                atom: atom.resolve(),
            },
            SymConstraint::CountFieldsEq { keys, value, reg } => {
                StateConstraint::FieldsCountEquals {
                    keys: keys.iter().map(|key| key.resolve(dep)).collect(),
                    value: field_from_u64(*value),
                    count_index: dep.reg(reg),
                }
            }
        }
    }
}

/// **Load the Lean-authored descent program**, resolving the symbolic slot/method names
/// against the allocator. Panics if the artifact fails to parse or names the wrong
/// scene — a corrupt/stale artifact must fail loud at deploy, never silently ship a
/// different program.
pub fn load_program(dep: &Deployment) -> CellProgram {
    load_program_for_day(dep, dep.day)
}

/// Parse the Lean-emitted family once. Panics loud on a corrupt/foreign artifact — a
/// stale cache must never silently ship a different program.
fn family() -> &'static SymProgram {
    static FAMILY: std::sync::OnceLock<SymProgram> = std::sync::OnceLock::new();
    FAMILY.get_or_init(|| {
        let sym: SymProgram =
            serde_json::from_str(PROGRAM_JSON).expect("dungeon_program.json (Lean-emitted) parses");
        assert_eq!(
            sym.scene, SCENE_ID,
            "Lean-emitted descent program scene mismatch (stale/foreign artifact)"
        );
        assert_eq!(
            sym.days, DAYS,
            "Lean-emitted family size disagrees with descent::DAYS (stale artifact)"
        );
        assert_eq!(sym.worlds.len(), DAYS, "one emitted program per drawn map");
        // [`HOME`] / [`CANON_WORLD`] are the only map numbers written in Rust (they exist
        // so day 0 is a `const`). Pin them to the Lean emission so they cannot drift:
        // a re-emit that moves day 0 fails LOUD here instead of silently disagreeing with
        // the teeth the executor installs.
        let day0 = sym
            .worlds
            .iter()
            .find(|w| w.day == 0)
            .expect("the family has a day 0");
        assert_eq!(
            day0.homes.as_slice(),
            CANON_WORLD.homes.as_slice(),
            "descent::HOME drifted from the Lean-emitted day 0 map"
        );
        assert_eq!(
            day0.ghp.as_slice(),
            CANON_WORLD.ghp.as_slice(),
            "descent::CANON_WORLD.ghp drifted from the Lean-emitted day 0 map"
        );
        sym
    })
}

/// **Load the Lean-authored descent program for family index `day`**, resolving the
/// symbolic slot/method names against the allocator. The day's map is a parameter of the
/// LEAN emit: every one of the `DAYS` case lists was authored in Lean for exactly its own
/// minted homes and guardian vitalities, so choosing a day is choosing an emitted
/// program, never editing one.
pub fn load_program_for_day(dep: &Deployment, day: usize) -> CellProgram {
    let sym = family();
    let world = sym
        .worlds
        .iter()
        .find(|w| w.day == day % DAYS)
        .expect("every day index in range has an emitted program");
    let cases = world
        .cases
        .iter()
        .map(|c| TransitionCase {
            guard: c.guard.resolve(dep),
            constraints: c.constraints.iter().map(|k| k.resolve(dep)).collect(),
        })
        .collect();
    CellProgram::Cases(cases)
}

// =============================================================================
// The mover — computes projections; the LOADED teeth are the referee.
// =============================================================================

/// The descent state as the mover tracks it (the Lean `DState`, custody-first:
/// `pack`/`bank`/`hoard` are PROJECTIONS of `custody`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sim {
    pub depth: u64,
    pub spent: u64,
    pub wounds: u64,
    /// **The run-long grip damage**, `0..=HARMCAP`. Unlike `wounds` (the standing
    /// guardian's tally, reset by [`Sim::delve`]), `harm` never resets and never
    /// decreases — it is subtracted from carrying rights for the rest of the run.
    pub harm: u64,
    pub fate: u64,
    /// `[way_2, way_3, way_4]`, each 0/1 (way 1 is always open).
    pub ways: [u64; 3],
    /// Per-relic custody code: `1..=4` deep at that floor, `8` carried, `9` banked.
    pub custody: [u64; RELICS],
    /// **The day's map** — where the relics were minted and how tough each floor's
    /// guardian is. The world is minted once and never moves during a run, which is why
    /// it rides the state: `guard_hp` and the genesis custody are functions of THIS, not
    /// of a compile-time constant (the Lean `WorldParam`).
    pub world: DayWorld,
}

impl Sim {
    /// The minted world for DAY 0 — the shipped map (the Lean `genesisState` at
    /// `instAt 0`).
    pub fn genesis() -> Self {
        Sim::genesis_on_day(0)
    }

    /// The minted world for family index `day` (the Lean `genesisState` at `instAt k`).
    pub fn genesis_on_day(day: usize) -> Self {
        Sim::genesis_in(day_world(day))
    }

    /// The minted world for an explicit drawn map.
    pub fn genesis_in(world: DayWorld) -> Self {
        Sim {
            depth: 0,
            spent: 0,
            wounds: 0,
            harm: 0,
            fate: 0,
            ways: [0, 0, 0],
            custody: world.homes,
            world,
        }
    }

    /// The standing floor's guardian vitality on THIS run's map (the Lean `guardHp`).
    pub fn guard_hp(&self, depth: u64) -> u64 {
        self.world.guard_hp(depth)
    }

    pub fn pack(&self) -> u64 {
        self.custody.iter().filter(|&&c| c == CARRIED).count() as u64
    }
    pub fn bank(&self) -> u64 {
        self.custody.iter().filter(|&&c| c == BANKED).count() as u64
    }
    pub fn hoard_at(&self, d: u64) -> u64 {
        self.custody.iter().filter(|&&c| c == d).count() as u64
    }
    pub fn way_open(&self, d: u64) -> bool {
        d <= 1 || (2..=FLOORS).contains(&d) && self.ways[(d - 2) as usize] == 1
    }

    fn alive_and_paid(&self, price: u64) -> Result<(), &'static str> {
        if self.fate != 0 {
            return Err("the run is banked — the tomb is frozen");
        }
        if self.spent + price > BREATH {
            return Err("the light dies — no breath left");
        }
        Ok(())
    }

    /// The delve rule (the Lean `step .delve`).
    pub fn delve(&self) -> Result<Sim, &'static str> {
        self.alive_and_paid(1)?;
        if self.depth >= FLOORS {
            return Err("the bottom");
        }
        if !self.way_open(self.depth + 1) {
            return Err("the way is shut — its key was never exercised");
        }
        if self.pack() + self.depth + 1 + self.harm > CAP {
            return Err("too laden to squeeze deeper (capacity attenuates)");
        }
        let mut s = self.clone();
        s.depth += 1;
        s.wounds = 0;
        s.spent += 1;
        Ok(s)
    }

    /// The unlock rule: EXERCISE the carried key-relic for way `w`.
    pub fn unlock(&self, w: u64) -> Result<Sim, &'static str> {
        self.alive_and_paid(1)?;
        if !(2..=FLOORS).contains(&w) {
            return Err("no such way");
        }
        if self.ways[(w - 2) as usize] != 0 {
            return Err("already open");
        }
        if self.custody[(w - 1) as usize] != CARRIED {
            return Err("the key-relic is not carried");
        }
        let mut s = self.clone();
        s.ways[(w - 2) as usize] = 1;
        s.spent += 1;
        Ok(s)
    }

    /// The smite rule: wound the standing guardian by exactly 1; it strikes back
    /// (price 2).
    pub fn smite(&self) -> Result<Sim, &'static str> {
        self.alive_and_paid(2)?;
        if self.depth < 1 {
            return Err("no guardian on the surface");
        }
        if self.wounds + 1 > self.guard_hp(self.depth) {
            return Err("the guardian is already slain");
        }
        let mut s = self.clone();
        s.wounds += 1;
        s.spent += 2;
        Ok(s)
    }

    /// **The lunge rule**: the same wound as [`smite`](Self::smite) for ONE breath,
    /// paid in grip (`harm += 1`). The capacity clause is the whole decision — at depth
    /// 1 it spends a carry slot you were never going to fill, at depth 4 it costs the
    /// prize (the Lean `step .lunge`).
    pub fn lunge(&self) -> Result<Sim, &'static str> {
        self.alive_and_paid(1)?;
        if self.depth < 1 {
            return Err("no guardian on the surface");
        }
        if self.wounds + 1 > self.guard_hp(self.depth) {
            return Err("the guardian is already slain");
        }
        if self.harm + 1 > HARMCAP {
            return Err("your grip is already broken — there is nothing left to give");
        }
        if self.pack() + self.depth + self.harm + 1 > CAP {
            return Err("a broken grip would spill what you carry (capacity attenuates)");
        }
        let mut s = self.clone();
        s.wounds += 1;
        s.spent += 1;
        s.harm += 1;
        Ok(s)
    }

    /// The loot rule: take relic `r` from the standing floor's hoard.
    pub fn loot(&self, r: usize) -> Result<Sim, &'static str> {
        self.alive_and_paid(1)?;
        if self.depth < 1 || r >= RELICS {
            return Err("nothing to loot");
        }
        if self.custody[r] != self.depth {
            return Err("the relic does not lie here");
        }
        if self.wounds != self.guard_hp(self.depth) {
            return Err("the guardian still stands");
        }
        if self.pack() + 1 + self.depth + self.harm > CAP {
            return Err("carrying rights exhausted (capacity attenuates)");
        }
        let mut s = self.clone();
        s.custody[r] = CARRIED;
        s.spent += 1;
        Ok(s)
    }

    /// The flee rule: bank the pack; the run ends.
    pub fn flee(&self) -> Result<Sim, &'static str> {
        self.alive_and_paid(1)?;
        let mut s = self.clone();
        for c in s.custody.iter_mut() {
            if *c == CARRIED {
                *c = BANKED;
            }
        }
        s.fate = 1;
        s.spent += 1;
        Ok(s)
    }
}

/// The domain tag for deriving a run's committed day-seed from its `u8` deploy seed, so a
/// plain [`Descent::deploy`] has a reproducible provenance root even without a supplied beacon.
const DAY_SEED_DOMAIN: &[u8] = b"dungeon-on-dregg/descent/day-seed/v1";

/// Derive the reproducible run day-seed a plain [`Descent::deploy`] mints its banked relics
/// under — a domain-separated hash of the deploy seed. [`Descent::deploy_on_day`] overrides this
/// with a real beacon day-seed; either way the day-seed is the provenance root a banked relic's
/// loot note is content-addressed under.
pub fn day_seed_from_deploy_seed(seed: u8) -> CommittedSeed {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&(DAY_SEED_DOMAIN.len() as u64).to_le_bytes());
    hasher.update(DAY_SEED_DOMAIN);
    hasher.update(&[seed]);
    CommittedSeed::from_bytes(*hasher.finalize().as_bytes())
}

/// A **banked relic minted as a real owned loot note** — the output of the bank → asset wire
/// ([`Descent::mint_banked_relics`]). `slot` is the relic's custody position on the run (its
/// identity); `item`'s [`AssetId`](dreggnet_asset::AssetId) provenance is content-addressed to
/// THIS banked relic (the run's day-seed + this slot), so it replays to the banked run rather
/// than to a manufactured draw.
#[derive(Clone, Debug)]
pub struct BankedRelicMint {
    /// The custody slot the relic banked in (relic 0 = the prize; 1–3 = way keys; 4–7 = treasures).
    pub slot: usize,
    /// The minted owned note whose provenance encodes this banked relic.
    pub item: LootItem,
}

/// A deployed descent on a real world-cell: the Lean-sourced teeth installed on the
/// real `EmbeddedExecutor`; every verb ONE cap-bounded turn.
pub struct Descent {
    dep: Deployment,
    world: WorldCell,
    sim: Sim,
    /// The run's committed day-seed — the provenance root a banked relic's minted loot note is
    /// content-addressed under (see [`Descent::mint_banked_relics`]).
    day_seed: CommittedSeed,
}

impl Descent {
    /// Deploy the Lean-loaded story on a real world-cell (deterministic in
    /// `SCENE_ID` + `seed`) and commit the one-shot genesis mint, on the SHIPPED map
    /// (family index 0). The run's committed day-seed — the provenance root a banked relic's loot
    /// note is minted under ([`mint_banked_relics`](Self::mint_banked_relics)) — is derived
    /// deterministically from `seed`, so a replay of the same deploy re-derives the same day-seed
    /// (hence the same minted notes).
    ///
    /// This is the reproducible dev/test entry: it pins day 0 so a fixed script stays a fixed
    /// dungeon. The DAILY entry is [`deploy_on_day`](Self::deploy_on_day), where the committed
    /// beacon day-seed draws the map as well as the loot provenance.
    pub fn deploy(seed: u8) -> Result<Self, WorldError> {
        Self::deploy_on_world(seed, day_seed_from_deploy_seed(seed), 0)
    }

    /// **THE DAILY.** Deploy on a world-cell birthed under `seed`, binding an explicit committed
    /// `day_seed` as the run's provenance root — and DRAWING THE DAY'S MAP FROM IT
    /// ([`day_index`]): which floor each relic (and each way-key) is minted on and how tough each
    /// floor's guardian is. The flagship supplies the verified drand-beacon day-seed, so the map is
    /// unpredictable-until-revealed exactly like the loot notes, and every drawn map is a
    /// Lean-checked, Lean-driven-completable dungeon (`Dungeon.draw_completable`).
    pub fn deploy_on_day(seed: u8, day_seed: CommittedSeed) -> Result<Self, WorldError> {
        let day = day_index(&day_seed);
        Self::deploy_on_world(seed, day_seed, day)
    }

    /// Deploy on an explicit family index — the shared body of [`deploy`] and
    /// [`deploy_on_day`], and the entry a replay uses when it already knows which map was played.
    pub fn deploy_on_world(
        seed: u8,
        day_seed: CommittedSeed,
        day: usize,
    ) -> Result<Self, WorldError> {
        let dep = Deployment::for_day(day);
        let story = dep.story();
        let world = WorldCell::deploy_compiled(Arc::new(story), seed)?;
        let genesis = Sim::genesis_on_day(dep.day);
        let mut game = Descent {
            dep,
            world,
            sim: genesis.clone(),
            day_seed,
        };
        game.world.apply_raw(GENESIS, game.effects_for(&genesis))?;
        game.sim = genesis;
        Ok(game)
    }

    pub fn dep(&self) -> &Deployment {
        &self.dep
    }
    /// The family index this run is being played on — which of the `DAYS` maps the
    /// committed day-seed drew.
    pub fn day(&self) -> usize {
        self.dep.day
    }
    /// The day's map: where each relic was minted, and each floor's guardian vitality.
    pub fn day_world(&self) -> DayWorld {
        self.sim.world
    }
    pub fn world(&self) -> &WorldCell {
        &self.world
    }
    pub fn sim(&self) -> &Sim {
        &self.sim
    }
    /// The run's committed day-seed — the provenance root a banked relic's minted loot note is
    /// content-addressed under. Reproducible from the deploy seed unless a real beacon day-seed
    /// was bound via [`deploy_on_day`](Self::deploy_on_day).
    pub fn day_seed(&self) -> &CommittedSeed {
        &self.day_seed
    }
    pub fn cell(&self) -> CellId {
        self.world.cell_id()
    }

    /// Every `SetField` effect that writes `sim` in full (14 registers + 8 relic keys).
    /// The counters are PROJECTIONS of custody — the mover cannot even express a
    /// count↔custody disagreement.
    pub fn effects_for(&self, sim: &Sim) -> Vec<Effect> {
        let cell = self.cell();
        let mut effects = Vec::with_capacity(REGISTERS.len() + RELICS);
        let mut set_reg = |name: &str, v: u64| {
            effects.push(Effect::SetField {
                cell,
                index: self.dep.reg(name) as u64,
                value: field_from_u64(v),
            });
        };
        // Keep the six proof-authored custody projections immediately
        // contiguous, in the same order as the census AIR public ABI.  A
        // shielded turn can prepend its `Effect::Custom` and the executor then
        // consumes exactly this SetField run as the mandatory app-write face.
        set_reg("pack", sim.pack());
        set_reg("bank", sim.bank());
        set_reg("hoard_1", sim.hoard_at(1));
        set_reg("hoard_2", sim.hoard_at(2));
        set_reg("hoard_3", sim.hoard_at(3));
        set_reg("hoard_4", sim.hoard_at(4));
        set_reg("depth", sim.depth);
        set_reg("spent", sim.spent);
        set_reg("wounds", sim.wounds);
        set_reg("fate", sim.fate);
        set_reg("way_2", sim.ways[0]);
        set_reg("way_3", sim.ways[1]);
        set_reg("way_4", sim.ways[2]);
        set_reg("harm", sim.harm);
        drop(set_reg);
        for (i, &c) in sim.custody.iter().enumerate() {
            effects.push(Effect::SetField {
                cell,
                index: self.dep.relic_key(i) as u64,
                value: field_from_u64(c),
            });
        }
        effects
    }

    fn commit_verb(
        &mut self,
        method: &str,
        next: Result<Sim, &'static str>,
    ) -> Result<TurnReceipt, WorldError> {
        let next = next.map_err(|e| WorldError::Refused(format!("mover: {e}")))?;
        let receipt = self.world.apply_raw(method, self.effects_for(&next))?;
        self.sim = next;
        Ok(receipt)
    }

    /// Commit one mover projection with a receipt-only event in the very same
    /// executor turn. This is crate-visible for the campaign engine: narration
    /// may describe a typed move, but the Lean-loaded referee remains the only
    /// authority over the projection.
    pub(crate) fn commit_projected_with_event(
        &mut self,
        method: &str,
        next: Result<Sim, &'static str>,
        event: Event,
    ) -> Result<TurnReceipt, WorldError> {
        let next = next.map_err(|error| WorldError::Refused(format!("mover: {error}")))?;
        let mut effects = self.effects_for(&next);
        effects.push(Effect::EmitEvent {
            cell: self.cell(),
            event,
        });
        let receipt = self.world.apply_raw(method, effects)?;
        self.sim = next;
        Ok(receipt)
    }

    pub fn delve(&mut self) -> Result<TurnReceipt, WorldError> {
        self.commit_verb(DELVE, self.sim.delve())
    }
    pub fn unlock(&mut self, w: u64) -> Result<TurnReceipt, WorldError> {
        self.commit_verb(UNLOCK, self.sim.unlock(w))
    }
    pub fn smite(&mut self) -> Result<TurnReceipt, WorldError> {
        self.commit_verb(SMITE, self.sim.smite())
    }
    pub fn lunge(&mut self) -> Result<TurnReceipt, WorldError> {
        self.commit_verb(LUNGE, self.sim.lunge())
    }
    pub fn loot(&mut self, r: usize) -> Result<TurnReceipt, WorldError> {
        self.commit_verb(LOOT, self.sim.loot(r))
    }
    pub fn flee(&mut self) -> Result<TurnReceipt, WorldError> {
        self.commit_verb(FLEE, self.sim.flee())
    }

    /// **Mint the run's BANKED relics as real owned loot notes** — the bank → asset wire that
    /// closes the gap between a banked custody relic (a real committed executor object) and a
    /// tradeable [`dreggnet_asset`] note. For each relic the run banked (`custody == BANKED`,
    /// reached only through a terminal [`flee`](Sim::flee)), this feeds the ACTUAL banked slot and
    /// the run's committed day-seed into [`LootVault::claim`] via
    /// [`banked_relic_drop`](crate::loot::banked_relic_drop). The minted note's
    /// [`AssetId`](dreggnet_asset::AssetId) provenance therefore encodes THE BANKED RELIC (the run
    /// day-seed + custody slot) and **replays to the banked run** — it is not a manufactured
    /// `roll_drop("boss:…")` draw. The mint is driven from the committed `sim.custody`, so a run
    /// that banked nothing mints nothing, and the `LootVault::claim` forged-claim gate still
    /// refuses any draw that is not the fair `(day_seed, slot)` drop. Returns one
    /// [`BankedRelicMint`] per banked relic, in slot order.
    pub fn mint_banked_relics(
        &self,
        vault: &mut LootVault,
        player: &str,
    ) -> Result<Vec<BankedRelicMint>, LootError> {
        let mut minted = Vec::new();
        for (slot, &custody) in self.sim.custody.iter().enumerate() {
            if custody == BANKED {
                let draw = banked_relic_drop(&self.day_seed, slot);
                let item = vault.claim(player, &draw)?;
                minted.push(BankedRelicMint { slot, item });
            }
        }
        Ok(minted)
    }

    /// Drive a raw turn (the illegal-move test builder): whatever `effects`, under
    /// `method`. The Lean-sourced referee decides.
    pub fn commit_raw(
        &self,
        method: &str,
        effects: Vec<Effect>,
    ) -> Result<TurnReceipt, WorldError> {
        self.world.apply_raw(method, effects)
    }

    /// A `SetField` on a named register (illegal-move test builder).
    pub fn reg_effect(&self, name: &str, v: u64) -> Effect {
        Effect::SetField {
            cell: self.cell(),
            index: self.dep.reg(name) as u64,
            value: field_from_u64(v),
        }
    }

    /// A `SetField` on a relic custody key (illegal-move test builder).
    pub fn relic_effect(&self, i: usize, v: u64) -> Effect {
        Effect::SetField {
            cell: self.cell(),
            index: self.dep.relic_key(i) as u64,
            value: field_from_u64(v),
        }
    }

    /// A full forged projection under `method`: `patch` mutates a copy of the current
    /// sim's effect list AFTER projection — the attack surface for the referee tests.
    pub fn read_reg(&self, name: &str) -> u64 {
        self.world.snapshot()[self.dep.reg(name) as usize]
    }

    pub fn read_relic(&self, i: usize) -> u64 {
        self.world.read_heap(self.dep.relic_key(i)).unwrap_or(0)
    }
}

/// **This day's crowned line** — the move tape that reaches the prize and banks it.
///
/// Lean PROVES such a line exists for every drawn map (`Dungeon.winsAt_true`,
/// `Dungeon.draw_completable : ∀ n, Completable (drawInst n)`) but the proof's witness does
/// not cross the FFI boundary, so callers used to hard-code day 0's tape and call it "the
/// exact crowned line from the Lean model". That was true of the one dungeon that existed
/// before the map became a function of the committed day-seed, and false on most of the
/// sixteen that exist now. This regenerates it from the day's own [`DayWorld`].
///
/// The construction mirrors the Lean `crownedRun` and leans on two facts the draw guarantees:
/// `homes (keyFor w) < w` (no key is minted behind the door it opens), so every key is in the
/// pack by the time its way is reached; and the prize sits at the bottom. Way `w`'s key is
/// relic `w - 1`, relic 0 is the prize, relics 4..7 are treasures this line deliberately
/// leaves lying — at depth `FLOORS` the pack holds three keys plus the prize, which is
/// exactly `CAP - FLOORS`, so taking a treasure would price the crown out of reach.
pub fn crowned_line(day: usize) -> Vec<(&'static str, i64)> {
    let world = day_world(day);
    let mut tape: Vec<(&'static str, i64)> = Vec::new();
    for floor in 1..=FLOORS {
        tape.push((DELVE, 0));
        // What the LINE needs from this floor: the way-keys (relics 1..FLOORS-1) and the prize
        // (relic 0), wherever the day minted them. Treasures are deliberately left lying — see
        // the capacity arithmetic below.
        let mut needed: Vec<i64> = Vec::new();
        for relic in 0..FLOORS {
            if world.homes[relic as usize] == floor {
                needed.push(relic as i64);
            }
        }
        // ⚑ ONLY FIGHT WHERE THERE IS SOMETHING TO TAKE. This mirrors Lean's `floorLine`:
        // "if anything needed lies here, fell the guardian and take it … a floor holding
        // nothing the line needs costs exactly one breath — the day's map decides where the
        // fighting happens." Smiting unconditionally is not merely wasteful, it is FATAL: on
        // day 9 (`ghp = [0,2,2,2,2]`) four needless felled guardians cost 16 breath and the
        // prize becomes unreachable inside BREATH. The first version of this function did
        // exactly that and the all-sixteen-days replay caught it.
        if !needed.is_empty() {
            for _ in 0..world.guard_hp(floor) {
                tape.push((SMITE, 0));
            }
            for relic in &needed {
                tape.push((LOOT, *relic));
            }
        }
        // Exercise every key won by now whose door is this floor's exit. Way `w`'s key is
        // relic `w - 1`, and the draw guarantees `homes (keyFor w) < w`, so it is carried.
        if floor < FLOORS {
            tape.push((UNLOCK, (floor + 1) as i64));
        }
    }
    tape.push((FLEE, 0));
    tape
}

#[cfg(test)]
mod crowned_line_tests {
    use super::*;

    /// The generated tape must actually CROWN, on every day the draw can produce — not on the
    /// one day someone happened to write down. This is the anti-vacuity guard for
    /// `crowned_line`: if the generator ever drifts from the map, some day stops banking.
    #[test]
    fn every_days_crowned_line_banks_the_prize_within_the_light() {
        for day in 0..DAYS {
            let mut sim = Sim::genesis_on_day(day);
            for (turn, arg) in crowned_line(day) {
                sim = match turn {
                    DELVE => sim.delve(),
                    SMITE => sim.smite(),
                    LOOT => sim.loot(arg as usize),
                    UNLOCK => sim.unlock(arg as u64),
                    FLEE => sim.flee(),
                    other => panic!("day {day}: crowned_line emitted unknown verb {other}"),
                }
                .unwrap_or_else(|e| panic!("day {day}: {turn}({arg}) refused: {e}"));
            }
            assert_eq!(
                sim.custody[0], BANKED,
                "day {day}: the crowned line did not bank the prize"
            );
            // ⚑ THE CROWN IS HARMLESS, on every day. The crowned line presses and never
            // lunges, so `harm` is 0 along it — which is exactly why the new capacity
            // term `pack + depth + harm <= CAP` degenerates to the old one here and
            // completability survived the change by construction rather than by luck.
            // This is the Rust half of `Dungeon.crowned_full_bank_harmless`.
            assert_eq!(sim.harm, 0, "day {day}: the crowned line must take no harm");
            assert!(
                sim.spent <= BREATH,
                "day {day}: the line costs {} of {BREATH} light",
                sim.spent
            );
        }
    }
}
