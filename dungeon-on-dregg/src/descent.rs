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
    CellId, CellProgram, Effect, StateConstraint, TransitionCase, TransitionGuard, TurnReceipt,
    field_from_u64, symbol,
};
use dregg_cell::program::{HeapAtom, SimpleStateConstraint};
use dregg_schema::layout::{CheckedLayout, Slot, allocate_checked};
use dregg_schema::schema::Schema;
use serde::Deserialize;
use spween_dregg::{CompiledStory, GENESIS_DONE_EXT_KEY, WorldCell, WorldError};

/// The scene id that fixes the deterministic world-cell identity (must match the Lean
/// emit's `Dregg2.Games.Dungeon.Prog.sceneId`).
pub const SCENE_ID: &str = "dungeon-on-dregg/descent1";

/// The one-shot mint (spween's genesis method name — the world births + writes the
/// genesis-done sentinel for it because the LOADED program's genesis case carries the
/// sentinel teeth).
pub const GENESIS: &str = "genesis";
pub const DELVE: &str = "delve";
pub const UNLOCK: &str = "unlock";
pub const SMITE: &str = "smite";
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
/// Relic mint homes: relic 0 = THE PRIZE (floor 4); relics 1–3 = the keys to ways 2–4;
/// relics 4–7 = treasures. (The Lean `homeFloors`.)
pub const HOME: [u64; RELICS] = [4, 1, 2, 3, 1, 1, 2, 3];

/// Per-floor guardian vitality (the Lean `guardHp`).
pub fn guard_hp(depth: u64) -> u64 {
    match depth {
        1 | 2 => 1,
        3 | 4 => 2,
        _ => 0,
    }
}

/// The 13 register components, in allocation order.
pub const REGISTERS: [&str; 13] = [
    "depth", "spent", "wounds", "fate", "pack", "bank", "way_2", "way_3", "way_4", "hoard_1",
    "hoard_2", "hoard_3", "hoard_4",
];

pub fn relic_name(i: usize) -> String {
    format!("relic_{i}")
}

/// Build the declared schema: 13 register components + 8 relic-custody collections.
pub fn schema() -> Schema {
    let mut s = Schema::new(SCENE_ID)
        .stat("depth", 0, FLOORS)
        .stat("spent", 0, BREATH)
        .stat("wounds", 0, 2)
        .stat("fate", 0, 1)
        .stat("pack", 0, RELICS as u64)
        .stat("bank", 0, RELICS as u64)
        .stat("way_2", 0, 1)
        .stat("way_3", 0, 1)
        .stat("way_4", 0, 1)
        .stat("hoard_1", 0, 3)
        .stat("hoard_2", 0, 2)
        .stat("hoard_3", 0, 2)
        .stat("hoard_4", 0, 1);
    for i in 0..RELICS {
        s = s.collection(relic_name(i));
    }
    s
}

/// The consumed, Legal-checked layout + the Lean-loaded teeth.
pub struct Deployment {
    pub layout: CheckedLayout,
}

impl Deployment {
    pub fn new() -> Self {
        let layout = allocate_checked(&schema()).expect("descent layout is Legal");
        Deployment { layout }
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

    /// The descent teeth, **LOADED from the Lean source of truth** — see
    /// [`load_program`]. No hand-rolled `CellProgram` exists in this crate for the
    /// descent; the deployed program IS the Lean object.
    pub fn program(&self) -> CellProgram {
        load_program(self)
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

#[derive(Debug, Deserialize)]
struct SymProgram {
    scene: String,
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
        }
    }
}

/// **Load the Lean-authored descent program**, resolving the symbolic slot/method names
/// against the allocator. Panics if the artifact fails to parse or names the wrong
/// scene — a corrupt/stale artifact must fail loud at deploy, never silently ship a
/// different program.
pub fn load_program(dep: &Deployment) -> CellProgram {
    let sym: SymProgram =
        serde_json::from_str(PROGRAM_JSON).expect("dungeon_program.json (Lean-emitted) parses");
    assert_eq!(
        sym.scene, SCENE_ID,
        "Lean-emitted descent program scene mismatch (stale/foreign artifact)"
    );
    let cases = sym
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
    pub fate: u64,
    /// `[way_2, way_3, way_4]`, each 0/1 (way 1 is always open).
    pub ways: [u64; 3],
    /// Per-relic custody code: `1..=4` deep at that floor, `8` carried, `9` banked.
    pub custody: [u64; RELICS],
}

impl Sim {
    /// The minted world (the Lean `genesisState`).
    pub fn genesis() -> Self {
        Sim {
            depth: 0,
            spent: 0,
            wounds: 0,
            fate: 0,
            ways: [0, 0, 0],
            custody: HOME,
        }
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
        if self.pack() + self.depth + 1 > CAP {
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
        if self.wounds + 1 > guard_hp(self.depth) {
            return Err("the guardian is already slain");
        }
        let mut s = self.clone();
        s.wounds += 1;
        s.spent += 2;
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
        if self.wounds != guard_hp(self.depth) {
            return Err("the guardian still stands");
        }
        if self.pack() + 1 + self.depth > CAP {
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

/// A deployed descent on a real world-cell: the Lean-sourced teeth installed on the
/// real `EmbeddedExecutor`; every verb ONE cap-bounded turn.
pub struct Descent {
    dep: Deployment,
    world: WorldCell,
    sim: Sim,
}

impl Descent {
    /// Deploy the Lean-loaded story on a real world-cell (deterministic in
    /// `SCENE_ID` + `seed`) and commit the one-shot genesis mint.
    pub fn deploy(seed: u8) -> Result<Self, WorldError> {
        let dep = Deployment::new();
        let story = dep.story();
        let world = WorldCell::deploy_compiled(Arc::new(story), seed)?;
        let mut game = Descent {
            dep,
            world,
            sim: Sim::genesis(),
        };
        let genesis = Sim::genesis();
        game.world.apply_raw(GENESIS, game.effects_for(&genesis))?;
        game.sim = genesis;
        Ok(game)
    }

    pub fn dep(&self) -> &Deployment {
        &self.dep
    }
    pub fn world(&self) -> &WorldCell {
        &self.world
    }
    pub fn sim(&self) -> &Sim {
        &self.sim
    }
    pub fn cell(&self) -> CellId {
        self.world.cell_id()
    }

    /// Every `SetField` effect that writes `sim` in full (13 registers + 8 relic keys).
    /// The counters are PROJECTIONS of custody — the mover cannot even express a
    /// count↔custody disagreement.
    pub fn effects_for(&self, sim: &Sim) -> Vec<Effect> {
        let cell = self.cell();
        let mut effects = Vec::with_capacity(13 + RELICS);
        let mut set_reg = |name: &str, v: u64| {
            effects.push(Effect::SetField {
                cell,
                index: self.dep.reg(name) as u64,
                value: field_from_u64(v),
            });
        };
        set_reg("depth", sim.depth);
        set_reg("spent", sim.spent);
        set_reg("wounds", sim.wounds);
        set_reg("fate", sim.fate);
        set_reg("pack", sim.pack());
        set_reg("bank", sim.bank());
        set_reg("way_2", sim.ways[0]);
        set_reg("way_3", sim.ways[1]);
        set_reg("way_4", sim.ways[2]);
        set_reg("hoard_1", sim.hoard_at(1));
        set_reg("hoard_2", sim.hoard_at(2));
        set_reg("hoard_3", sim.hoard_at(3));
        set_reg("hoard_4", sim.hoard_at(4));
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

    pub fn delve(&mut self) -> Result<TurnReceipt, WorldError> {
        self.commit_verb(DELVE, self.sim.delve())
    }
    pub fn unlock(&mut self, w: u64) -> Result<TurnReceipt, WorldError> {
        self.commit_verb(UNLOCK, self.sim.unlock(w))
    }
    pub fn smite(&mut self) -> Result<TurnReceipt, WorldError> {
        self.commit_verb(SMITE, self.sim.smite())
    }
    pub fn loot(&mut self, r: usize) -> Result<TurnReceipt, WorldError> {
        self.commit_verb(LOOT, self.sim.loot(r))
    }
    pub fn flee(&mut self) -> Result<TurnReceipt, WorldError> {
        self.commit_verb(FLEE, self.sim.flee())
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
