//! # The dungeon ruleset IR — pure data, ported from `attested-dm`'s `game.rs`.
//!
//! The `.dungeon` parser ([`super::parse`]) and validator ([`super::validate`]) speak in
//! these types; the compiler ([`super::compile`]) lowers them onto the REAL substrate.
//! This is a lift-and-shift of exactly the PURE subset of `attested-dm/src/game.rs` the
//! DSL needs — the static ruleset data structures — with every method that touched
//! attested-dm's toy `WorldCell`/blake3 ledger left behind (a `Gate` here does not know
//! how to check itself against a world; the compiler lowers it to an executor tooth
//! instead).
//!
//! Deliberate deviations from the source of the port (named, not silent):
//! * `GameWorld.loot` / `GameWorld.encounters` are DROPPED. The `.dungeon` grammar has
//!   no directive that can populate them (attested-dm's own `build()` always emits
//!   empty vectors), so carrying `LootRule`/`EncounterRule` — and the combat subsystem
//!   they pull in — would be dead weight. [`GameWorld::all_items`] loses its loot-table
//!   union arm accordingly; for any world this module can represent the result is
//!   identical.
//! * World-state helpers (`Gate::satisfied`, `LightRule::oil`, `StatusRule::active`, …)
//!   are not ported: they read attested-dm's `WorldCell`. Pure helpers
//!   ([`GameWorld::all_items`], [`GameWorld::is_spell_word`], [`GameWorld::npc_here`],
//!   [`LightRule::is_dark`]) are kept — the validator uses them.

use std::collections::{BTreeMap, BTreeSet};

// ─────────────────────────────────────────────────────────────────────────────
// Gates, exits, rooms.
// ─────────────────────────────────────────────────────────────────────────────

/// **A requirement that blocks an exit until met** — the deterministic lock. The
/// compiler lowers a gated exit to a real executor `StateConstraint` (see
/// [`super::compile`]); the validator checks the gate's referent exists.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Gate {
    /// The exit is open only while the player HOLDS `item` (e.g. the lantern lights a
    /// dark stair).
    NeedsItem(String),
    /// The exit is open only while world flag `k >= v` (e.g. `door_unlocked >= 1`).
    NeedsFlag(String, i64),
}

/// An exit from a room — where it leads, and the (optional) [`Gate`] that must be met
/// to pass.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Exit {
    /// The destination room id.
    pub to_room: String,
    /// The requirement that blocks this exit, or `None` for an always-open passage.
    pub gate: Option<Gate>,
}

impl Exit {
    /// An always-open exit to `to_room`.
    pub fn open(to_room: impl Into<String>) -> Exit {
        Exit {
            to_room: to_room.into(),
            gate: None,
        }
    }

    /// An exit to `to_room` blocked by `gate` until it is satisfied.
    pub fn gated(to_room: impl Into<String>, gate: Gate) -> Exit {
        Exit {
            to_room: to_room.into(),
            gate: Some(gate),
        }
    }
}

/// A room in the dungeon — its name, description, gated exits (keyed by direction),
/// and the items initially resting here.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Room {
    /// The room's stable id.
    pub id: String,
    /// The room's short name.
    pub name: String,
    /// A vivid description (pure narration; never load-bearing).
    pub description: String,
    /// Exits keyed by direction (`"north"`, `"down"`, …), each with its optional gate.
    pub exits: BTreeMap<String, Exit>,
    /// The items initially in this room.
    pub items: BTreeSet<String>,
}

impl Room {
    /// A room builder.
    pub fn new(
        id: impl Into<String>,
        name: impl Into<String>,
        description: impl Into<String>,
    ) -> Room {
        Room {
            id: id.into(),
            name: name.into(),
            description: description.into(),
            exits: BTreeMap::new(),
            items: BTreeSet::new(),
        }
    }

    /// Add an exit in `dir` and return `self` (builder style).
    pub fn exit(mut self, dir: impl Into<String>, exit: Exit) -> Room {
        self.exits.insert(dir.into(), exit);
        self
    }

    /// Place an item here and return `self` (builder style).
    pub fn item(mut self, item: impl Into<String>) -> Room {
        self.items.insert(item.into());
        self
    }
}

/// **A `Use` interaction the world defines.** When the player uses `item` (optionally
/// on `target`) in `room`, world flag `sets_flag` is set. This is how a key opens a
/// door: the gated exit reads the flag this rule sets.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UseRule {
    /// The room this interaction is available in.
    pub room: String,
    /// The (held) item that triggers it.
    pub item: String,
    /// The target it must be used on, or `None` if the item is used bare.
    pub target: Option<String>,
    /// The world flag the interaction sets (name, value).
    pub sets_flag: (String, i64),
    /// The world's account of what the interaction does.
    pub narration: String,
}

/// **A one-shot hostile in a room.** Defeated only if the player holds `defeated_by`;
/// otherwise the attacker is slain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Hostile {
    /// The room the hostile guards.
    pub room: String,
    /// The hostile's name (the attack target).
    pub name: String,
    /// The item that lets the player defeat it (e.g. the sword).
    pub defeated_by: String,
    /// The flag set on victory, which downstream gates read.
    pub victory_flag: (String, i64),
    /// The flag set on the player's death (a lose flag; see [`LoseCondition`]).
    pub death_flag: (String, i64),
    /// The world's account of a victorious strike.
    pub victory_narration: String,
    /// The world's account of the fatal strike.
    pub death_narration: String,
}

// ─────────────────────────────────────────────────────────────────────────────
// NPCs + bounded dialogue.
// ─────────────────────────────────────────────────────────────────────────────

/// **A non-player character standing in a room.** What the NPC actually *does* is
/// decided by the world's [`DialogueRule`]s, never by prose.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Npc {
    /// The room the NPC is in.
    pub room: String,
    /// The NPC's stable id (the dialogue target).
    pub id: String,
    /// The NPC's display name.
    pub name: String,
    /// A short line of who they are.
    pub description: String,
}

impl Npc {
    /// An NPC builder.
    pub fn new(
        room: impl Into<String>,
        id: impl Into<String>,
        name: impl Into<String>,
        description: impl Into<String>,
    ) -> Npc {
        Npc {
            room: room.into(),
            id: id.into(),
            name: name.into(),
            description: description.into(),
        }
    }
}

/// **What an NPC's words are permitted to DO** when its [`DialogueRule`]'s condition
/// holds. An NPC can never conjure an item the world never registered.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DialogueGrant {
    /// The NPC hands over a world-registered ([`GameWorld::all_items`]) item.
    GivesItem(String),
    /// The NPC opens the way by setting a flag a downstream [`Gate`] reads.
    OpensFlag(String, i64),
    /// The NPC only speaks — no world change (a pure narration turn).
    Reveals,
}

/// **A bounded thing an NPC can be made to do by talking to it.** If `requires` is
/// `None` or satisfied, the `grant` fires with `granted_narration`; otherwise the NPC
/// speaks (`withheld_narration`) but grants NOTHING.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DialogueRule {
    /// The room the conversation happens in.
    pub room: String,
    /// The NPC addressed (its [`Npc::id`]).
    pub npc: String,
    /// The topic asked about.
    pub topic: String,
    /// The world-condition under which the NPC's words have POWER.
    pub requires: Option<Gate>,
    /// What the NPC does when `requires` holds.
    pub grant: DialogueGrant,
    /// The world's account when the grant fires.
    pub granted_narration: String,
    /// The world's account when `requires` is not met.
    pub withheld_narration: String,
}

// ─────────────────────────────────────────────────────────────────────────────
// HP combat.
// ─────────────────────────────────────────────────────────────────────────────

/// **A combat foe with HIT POINTS and a multi-turn fight** — the deeper combat model
/// beside the one-shot [`Hostile`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CombatEnemy {
    /// The room the foe holds.
    pub room: String,
    /// The foe's name (the attack target).
    pub name: String,
    /// The foe's hit points — accumulated wounds `>= hp` fells it.
    pub hp: i64,
    /// The item that lets you wound it meaningfully.
    pub armed_by: String,
    /// Damage one strike deals WHILE you hold `armed_by`.
    pub weapon_damage: i64,
    /// Damage one strike deals WITHOUT the weapon.
    pub unarmed_damage: i64,
    /// Damage the foe deals to you on each round it SURVIVES.
    pub attack: i64,
    /// An optional armor item and the damage it mitigates per hit.
    pub armor: Option<(String, i64)>,
    /// The flag set once the foe is felled.
    pub victory_flag: (String, i64),
    /// The world's account of the felling blow.
    pub victory_narration: String,
    /// The world's account of a strike that wounds the foe but does not fell it.
    pub hit_narration: String,
    /// The world's account of a strike that fails to wound the foe.
    pub flail_narration: String,
}

// ─────────────────────────────────────────────────────────────────────────────
// Spells.
// ─────────────────────────────────────────────────────────────────────────────

/// **The bounded effect a spell is permitted to have** when cast, learned, in the
/// right context.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SpellEffect {
    /// Set a world flag (name, value).
    SetFlag(String, i64),
    /// Conjure a **world-registered** item into the caster's hand.
    Conjure(String),
    /// A combat/precondition **buff flag** (name, value).
    Buff(String, i64),
}

/// **A spell WORD the world declares to exist**, and what it takes to have LEARNED it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Spell {
    /// The incantation word (e.g. `"light"`).
    pub word: String,
    /// The world-condition under which the caster has LEARNED this word; `None` means
    /// innately known.
    pub learned: Option<Gate>,
}

/// **A CONTEXT in which a learned spell does its bounded thing.**
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpellRule {
    /// The room the spell has an effect in.
    pub room: String,
    /// The spell word this rule governs (its [`Spell::word`]).
    pub spell: String,
    /// The target the cast must be aimed at, or `None` if cast bare.
    pub target: Option<String>,
    /// An optional extra precondition beyond having LEARNED the word.
    pub requires: Option<Gate>,
    /// The bounded thing the spell does when cast correctly.
    pub effect: SpellEffect,
    /// The world's account when the spell fires.
    pub narration: String,
    /// The world's account when a matching rule's `requires` is unmet.
    pub fizzle_narration: String,
}

// ─────────────────────────────────────────────────────────────────────────────
// Light (a per-step resource).
// ─────────────────────────────────────────────────────────────────────────────

/// **A world-declared LIGHT budget** — a lit lamp burns down one turn per step, dark
/// rooms are impassable without it, and single-use oil refuels it.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct LightRule {
    /// The world flag holding the remaining lamp-turns.
    pub counter: String,
    /// The lamp item.
    pub lamp: String,
    /// The lamp's initial oil.
    pub start: i64,
    /// The pitch-dark rooms.
    pub dark_rooms: BTreeSet<String>,
    /// The single-use refuel interactions.
    pub refuels: Vec<RefuelRule>,
    /// The flag set when the lamp gutters out in the dark (a stranded LOSE), or `None`.
    pub stranded: Option<(String, i64)>,
}

impl LightRule {
    /// Whether `room` is pitch dark (needs a burning lamp to enter).
    pub fn is_dark(&self, room: &str) -> bool {
        self.dark_rooms.contains(room)
    }

    /// The refuel rule for pouring `fuel_item` into the lamp, if the world declares one.
    pub fn refuel_for(&self, fuel_item: &str) -> Option<&RefuelRule> {
        self.refuels.iter().find(|r| r.fuel_item == fuel_item)
    }
}

/// **A single-use REFUEL interaction** — pour oil into the lamp to buy more turns.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RefuelRule {
    /// The oil the player must HOLD to refuel.
    pub fuel_item: String,
    /// The turns added to the light counter on a successful pour.
    pub add: i64,
    /// The per-flask guard flag: once set, this flask is spent.
    pub spent_flag: String,
    /// The world's account of a successful refuel.
    pub narration: String,
    /// The world's account of pouring an already-spent flask.
    pub spent_narration: String,
}

// ─────────────────────────────────────────────────────────────────────────────
// Consumables + statuses.
// ─────────────────────────────────────────────────────────────────────────────

/// **What a status FLAG does while it is active** (its counter `> 0`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StatusKind {
    /// A BUFF: while active, mitigates `mitigate` damage off every blow.
    Shield(i64),
    /// A DEBUFF: while active, adds `damage` to the player's wounds on every step.
    Poison(i64),
}

/// **A timed status the world declares** — a buff/debuff carried as a world flag
/// holding its remaining turns.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StatusRule {
    /// The world flag holding this status's remaining turns (`> 0` = active).
    pub flag: String,
    /// What the status does while active.
    pub kind: StatusKind,
}

/// **The bounded effect a consumable has when it is `use`d.**
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConsumableEffect {
    /// Reduce the player's wounds by `n`, clamped at zero.
    Heal(i64),
    /// Grant a timed status: set the named status flag to `duration` turns.
    Status {
        /// The status flag to set (a declared [`StatusRule::flag`]).
        flag: String,
        /// The number of turns to grant.
        duration: i64,
    },
    /// Cure a status: set the named status flag to zero.
    Cure(String),
    /// Set a plain world flag (name, value).
    SetFlag(String, i64),
    /// No world change beyond the consumption.
    Reveal,
}

/// **A consumable the world declares** — an item that, when `use`d, does a bounded
/// [`ConsumableEffect`] and is CONSUMED.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConsumableRule {
    /// The item that is consumed. Must be world-registered ([`GameWorld::all_items`]).
    pub item: String,
    /// The bounded effect the consumable has when used.
    pub effect: ConsumableEffect,
    /// The world's account of using it.
    pub narration: String,
}

// ─────────────────────────────────────────────────────────────────────────────
// Objective, lose conditions, the world.
// ─────────────────────────────────────────────────────────────────────────────

/// **The win condition** — reach `room` while HOLDING `holding`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Objective {
    /// The room the player must reach.
    pub room: String,
    /// The item the player must be holding when they reach it.
    pub holding: String,
}

/// **A lose condition** — the game is LOST once world flag `flag >= at_least`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoseCondition {
    /// The flag that, once set high enough, ends the game in defeat.
    pub flag: String,
    /// The threshold.
    pub at_least: i64,
    /// A legible description of the defeat.
    pub description: String,
}

/// **The static dungeon** — the rooms, rules, starting room, win objective, and lose
/// conditions. Pure data; it never mutates.
#[derive(Clone, Debug)]
pub struct GameWorld {
    /// The rooms, keyed by id.
    pub rooms: BTreeMap<String, Room>,
    /// The `Use` interactions the world defines.
    pub use_rules: Vec<UseRule>,
    /// The one-shot hostiles, keyed by the room they guard.
    pub hostiles: BTreeMap<String, Hostile>,
    /// The HP-bearing combat foes, keyed by the room they guard.
    pub combat: BTreeMap<String, CombatEnemy>,
    /// The NPCs standing in the world.
    pub npcs: Vec<Npc>,
    /// The bounded dialogue rules — what talking to an NPC can actually DO.
    pub dialogue: Vec<DialogueRule>,
    /// The spell WORDS this world declares to exist.
    pub spells: Vec<Spell>,
    /// The bounded spell CONTEXTS — what a learned spell does, where.
    pub spell_rules: Vec<SpellRule>,
    /// The consumables this world declares.
    pub consumables: Vec<ConsumableRule>,
    /// The timed statuses this world declares.
    pub statuses: Vec<StatusRule>,
    /// The player's maximum hit points (combat dungeons only; `0` = no HP dimension).
    pub player_max_hp: i64,
    /// The optional LIGHT budget, or `None` for a dungeon with no light dimension.
    pub light: Option<LightRule>,
    /// The starting room id.
    pub start: String,
    /// The win objective.
    pub objective: Objective,
    /// The lose conditions.
    pub lose: Vec<LoseCondition>,
}

impl GameWorld {
    /// The room with `id`, if any.
    pub fn room(&self, id: &str) -> Option<&Room> {
        self.rooms.get(id)
    }

    /// The set of grantable items across the whole dungeon: the union of every item
    /// placed in a room, every item an NPC can hand over, and every item a spell can
    /// conjure. An item outside this set is unregistered and ungrantable.
    pub fn all_items(&self) -> BTreeSet<String> {
        let mut items: BTreeSet<String> = self
            .rooms
            .values()
            .flat_map(|r| r.items.iter().cloned())
            .collect();
        for rule in &self.dialogue {
            if let DialogueGrant::GivesItem(i) = &rule.grant {
                items.insert(i.clone());
            }
        }
        for rule in &self.spell_rules {
            if let SpellEffect::Conjure(i) = &rule.effect {
                items.insert(i.clone());
            }
        }
        items
    }

    /// Whether `word` is a spell this world declares (its casting vocabulary).
    pub fn is_spell_word(&self, word: &str) -> bool {
        self.spells.iter().any(|s| s.word == word)
    }

    /// Whether an NPC with id `npc` stands in `room`.
    pub fn npc_here(&self, room: &str, npc: &str) -> bool {
        self.npcs.iter().any(|n| n.room == room && n.id == npc)
    }
}
