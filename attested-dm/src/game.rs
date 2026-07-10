//! # game — the dungeon-crawler ENGINE: the AI proposes, the world disposes.
//!
//! attested-dm's [`crate::DungeonMaster`] proves a narration is authentic, well-formed,
//! injection-free, cap-bounded, and on-chain. This module is the layer that makes it a
//! *game*: a [`GameWorld`] of rooms / items / gated exits with an [`Objective`], and a
//! deterministic [`resolve_action`] that decides what a move actually does — regardless of
//! how the AI narrates it.
//!
//! ## Prose is not power, at the level of a game move
//!
//! Each turn, the AI dungeon-master (the [`GameBrain`] — the modeled [`ScriptedGm`] here,
//! a real gemma2 in the flagship) does two things: it **narrates** the room + the move
//! vividly, and it **proposes a [`GameAction`]** — a *closed typed* channel: `Move`,
//! `Take`, `Use`, `Examine`, `Attack`. It cannot free-text a world mutation; it can only
//! name one of these moves. Then the **world resolves**:
//!
//! * [`GameAction::Move`] succeeds only through an OPEN exit — a [`Gate`]d exit is REFUSED
//!   ("the door is locked") until its requirement (a held item, or a set flag) is met.
//! * [`GameAction::Take`] succeeds only for an item PRESENT in the current room.
//! * [`GameAction::Use`] needs an item you HOLD, and applies only a rule the world defines
//!   (e.g. use the key on the iron door → the door-unlocked flag sets → the gated exit opens).
//! * [`GameAction::Attack`] resolves by the world's rules — the Warden falls to the sword,
//!   or cuts you down if you lack it.
//!
//! A jailbroken model that narrates *"the iron door swings wide and you stride through"*
//! changes **nothing** if the door is locked: it can only propose `Move`, and the resolver
//! refuses it ([`Outcome::Refused`]) — the world unchanged, **no receipt** (the anti-ghost
//! tooth). The narration is discarded; the state does not move. Only a **legal** move is
//! attested and appended to the chain as ONE verified turn carrying its [`GameBinding`].
//!
//! ## The two teeth, both kept
//!
//! * **The resolver** gates every move by the world's rules (you cannot narrate through a
//!   locked door, take an absent item, or win without the amulet).
//! * **[`crate::DmCaps`]** still gates grants: the DM can only propose `GrantItem` for an
//!   item on its whitelist, so it cannot mint an item the world never placed. The engine's
//!   takeable items are exactly the DM's grantable set — the resolver only ever proposes a
//!   grant for an item actually present, and the cap is the second, independent bound.

use std::collections::{BTreeMap, BTreeSet};

use crate::{
    slot_confined, world_binding, DmError, DmMove, DungeonMaster, PromptBinding, Receipt,
    RecordedDm, WorldCell, WorldEffect,
};

// ─────────────────────────────────────────────────────────────────────────────
// The closed typed action channel — the ONLY moves the AI can propose.
// ─────────────────────────────────────────────────────────────────────────────

/// **The closed, typed action a dungeon-master may propose.** This is the whole channel
/// through which the AI can attempt to change the world — it cannot emit free-text state
/// mutations, only *name* one of these moves. The [`resolve_action`] resolver then decides
/// what (if anything) actually happens. Riding the chain via [`GameBinding`], the on-ledger
/// receipt commits to exactly which typed move produced each turn.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GameAction {
    /// Move toward a destination — named either by a room id or by an exit direction
    /// (`"north"`, `"down"`, …). Succeeds only through an OPEN exit from the current room.
    Move(String),
    /// Take an item from the current room. Succeeds only if the item is PRESENT here.
    Take(String),
    /// Use a held item, optionally on a target (e.g. `Use("rusted_key", Some("iron_door"))`).
    /// Succeeds only if you HOLD the item and the world defines a [`UseRule`] for it here.
    Use(String, Option<String>),
    /// Look at the current room — a pure-narration move (no world-effect), always legal.
    Examine,
    /// Attack a target in the current room. Resolves by the world's [`Hostile`] rules.
    Attack(String),
}

impl GameAction {
    /// **Address an NPC** — talk to `npc` about `topic`. Talking is narration: this rides the
    /// closed [`GameAction::Use`] channel (its target is the NPC), and the resolver grants only
    /// what a world [`DialogueRule`] permits. Pass an empty `topic` for a bare greeting.
    pub fn talk(npc: impl Into<String>, topic: impl Into<String>) -> GameAction {
        GameAction::Use(topic.into(), Some(npc.into()))
    }

    /// A short human-legible label for the action (for playthrough logs).
    pub fn label(&self) -> String {
        match self {
            GameAction::Move(to) => format!("move -> {to}"),
            GameAction::Take(i) => format!("take {i}"),
            GameAction::Use(i, Some(t)) => format!("use {i} on {t}"),
            GameAction::Use(i, None) => format!("use {i}"),
            GameAction::Examine => "examine".to_string(),
            GameAction::Attack(t) => format!("attack {t}"),
        }
    }

    /// Deterministic, tagged, length-prefixed encoding into the chain hash — so a rewritten
    /// action (claiming a different move produced a landed turn) breaks the receipt.
    pub(crate) fn encode_into(&self, h: &mut blake3::Hasher) {
        fn s(h: &mut blake3::Hasher, x: &str) {
            h.update(&(x.len() as u64).to_le_bytes());
            h.update(x.as_bytes());
        }
        match self {
            GameAction::Move(to) => {
                h.update(&[1u8]);
                s(h, to);
            }
            GameAction::Take(i) => {
                h.update(&[2u8]);
                s(h, i);
            }
            GameAction::Use(i, t) => {
                h.update(&[3u8]);
                s(h, i);
                match t {
                    None => {
                        h.update(&[0u8]);
                    }
                    Some(t) => {
                        h.update(&[1u8]);
                        s(h, t);
                    }
                }
            }
            GameAction::Examine => {
                h.update(&[4u8]);
            }
            GameAction::Attack(t) => {
                h.update(&[5u8]);
                s(h, t);
            }
        }
    }
}

/// **The game-move binding a landed turn carries** — the closed typed [`GameAction`] the
/// resolver admitted, and the room it acted in. Bound into the turn's receipt (see
/// [`crate::chain_receipt_id`]) so the chain commits to the sequence of *moves*, not just the
/// prose: a rewritten action or swapped room breaks the link.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GameBinding {
    /// The typed action the resolver admitted this turn.
    pub action: GameAction,
    /// The room id the action was resolved in.
    pub room: String,
}

impl GameBinding {
    /// A binding over an admitted action + the room it resolved in.
    pub fn new(action: GameAction, room: impl Into<String>) -> GameBinding {
        GameBinding {
            action,
            room: room.into(),
        }
    }

    /// Deterministic encoding into the chain hash (room ‖ action).
    pub(crate) fn encode_into(&self, h: &mut blake3::Hasher) {
        h.update(&(self.room.len() as u64).to_le_bytes());
        h.update(self.room.as_bytes());
        self.action.encode_into(h);
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The static world — rooms, gated exits, items, use-rules, hostiles, objective.
// ─────────────────────────────────────────────────────────────────────────────

/// **A requirement that blocks an exit until met** — the deterministic lock. A gated exit is
/// REFUSED until its gate is satisfied by the current world state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Gate {
    /// The exit is open only while the player HOLDS `item` (e.g. the lantern lights a dark stair).
    NeedsItem(String),
    /// The exit is open only while world flag `k >= v` (e.g. `door_unlocked >= 1`).
    NeedsFlag(String, i64),
}

impl Gate {
    fn satisfied(&self, world: &WorldCell) -> bool {
        match self {
            Gate::NeedsItem(i) => world.inventory.contains(i),
            Gate::NeedsFlag(k, v) => world.flags.get(k).copied().unwrap_or(0) >= *v,
        }
    }

    fn reason(&self) -> GateReason {
        match self {
            Gate::NeedsItem(i) => GateReason::NeedsItem(i.clone()),
            Gate::NeedsFlag(k, v) => GateReason::NeedsFlag(k.clone(), *v),
        }
    }
}

/// The legible reason a gated exit refused a move.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GateReason {
    /// The exit needs a held item the player lacks.
    NeedsItem(String),
    /// The exit needs a world flag not yet set high enough.
    NeedsFlag(String, i64),
}

impl std::fmt::Display for GateReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GateReason::NeedsItem(i) => write!(f, "it needs the {i}"),
            GateReason::NeedsFlag(k, v) => write!(f, "it stays sealed until {k} >= {v}"),
        }
    }
}

/// An exit from a room — where it leads, and the (optional) [`Gate`] that must be met to pass.
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

/// A room in the dungeon — its name, description, gated exits (keyed by direction), and the
/// items initially resting here.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Room {
    /// The room's stable id (the value stored in [`WorldCell::scene`]).
    pub id: String,
    /// The room's short name.
    pub name: String,
    /// A vivid description (the world's own account; the AI narrates *around* it).
    pub description: String,
    /// Exits keyed by direction (`"north"`, `"down"`, …), each with its optional gate.
    pub exits: BTreeMap<String, Exit>,
    /// The items initially in this room. An item is "here" until it is taken into inventory.
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

/// **A `Use` interaction the world defines.** When the player uses `item` (optionally on
/// `target`) in `room`, world flag `sets_flag` is set. This is how a key opens a door: the
/// gated exit reads the flag this rule sets.
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

/// **A hostile in a room** — resolves [`GameAction::Attack`]. Defeated only if the player
/// holds `defeated_by`; otherwise the attacker is slain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Hostile {
    /// The room the hostile guards.
    pub room: String,
    /// The hostile's name (the `Attack` target).
    pub name: String,
    /// The item that lets the player defeat it (e.g. the sword).
    pub defeated_by: String,
    /// The flag set on victory (e.g. `warden_defeated = 1`), which downstream gates read.
    pub victory_flag: (String, i64),
    /// The flag set on the player's death (a lose flag; see [`LoseCondition`]).
    pub death_flag: (String, i64),
    /// The world's account of a victorious strike.
    pub victory_narration: String,
    /// The world's account of the fatal strike (the player dies).
    pub death_narration: String,
}

// ─────────────────────────────────────────────────────────────────────────────
// NPCs + BOUNDED dialogue — the AI narrates the reply; the WORLD resolves what the
// NPC's words can DO. Prose is not power, at the social level.
// ─────────────────────────────────────────────────────────────────────────────

/// **A non-player character standing in a room.** The AI narrates its voice vividly, but what
/// the NPC actually *does* — hand over an item, open a gate, reveal a fact — is decided by the
/// world's [`DialogueRule`]s, never by the prose. A jailbroken narrator that makes the NPC
/// "press the master key into your hand" changes nothing: talking is a [`GameAction::Use`]
/// addressed to the NPC, and the resolver grants only what a rule (whose world-condition holds)
/// permits.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Npc {
    /// The room the NPC is in.
    pub room: String,
    /// The NPC's stable id (the `Use` *target* that addresses it — e.g. `Use("passage", Some("ferryman"))`).
    pub id: String,
    /// The NPC's display name.
    pub name: String,
    /// A short line of who they are (the world's own account; the AI narrates around it).
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

/// **What an NPC's words are permitted to DO** when its [`DialogueRule`]'s condition holds.
/// This is the whole social affordance: an NPC can give a (world-registered) item, open a gate
/// by setting a flag, or reveal a fact (pure lore, no world change). It can never conjure an
/// item the world never registered — a `GivesItem` grant is cap-gated exactly like a `Take`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DialogueGrant {
    /// The NPC hands over an item. It must be a world-registered ([`GameWorld::all_items`])
    /// item, so the grant is cap-permitted — an NPC cannot mint an unplaced item.
    GivesItem(String),
    /// The NPC opens the way / changes the world by setting a flag a downstream [`Gate`] reads.
    OpensFlag(String, i64),
    /// The NPC only speaks — reveals a fact, gives a hint. No world change (a pure narration turn).
    Reveals,
}

/// **A bounded thing an NPC can be made to do by talking to it.** When the player addresses
/// `npc` about `topic` in `room` (a [`GameAction::Use`] whose target is the NPC), the resolver
/// finds the matching rule. If `requires` is `None` or satisfied by the current world, the
/// NPC's `grant` fires and `granted_narration` is the world's account; otherwise the NPC still
/// speaks (`withheld_narration`) but grants NOTHING — the conversation lands as a pure-narration
/// turn. This is the social-level anti-forgery tooth: the Ferryman gives passage only while you
/// hold the coin, no matter how sweetly the AI narrates him handing you the keys to the kingdom.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DialogueRule {
    /// The room the conversation happens in.
    pub room: String,
    /// The NPC addressed (its [`Npc::id`]).
    pub npc: String,
    /// The topic asked about. An empty player topic matches the NPC's first rule in the room.
    pub topic: String,
    /// The world-condition under which the NPC's words have POWER (its `grant` fires). `None`
    /// means the NPC always obliges (e.g. a scholar who simply tells you a fact).
    pub requires: Option<Gate>,
    /// What the NPC does when `requires` holds.
    pub grant: DialogueGrant,
    /// The world's account when the grant fires.
    pub granted_narration: String,
    /// The world's account when `requires` is not met — the NPC speaks, but grants nothing.
    pub withheld_narration: String,
}

/// **A combat foe with HIT POINTS and a multi-turn fight** — the deeper combat model beside the
/// one-shot [`Hostile`]. Each [`GameAction::Attack`] is one exchange the WORLD resolves: your
/// armed strike takes `weapon_damage` off the foe (an unarmed strike only `unarmed_damage`); if
/// the foe survives it strikes back for `attack` (mitigated by held `armor`). Both totals are
/// tracked as world flags across turns (the foe's accumulated wounds and your `player_wounds`),
/// so you defeat it over several turns with the right weapon — or die over several turns without
/// it. The AI narrates each blow; the world computes the HP and the outcome.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CombatEnemy {
    /// The room the foe holds.
    pub room: String,
    /// The foe's name (the `Attack` target).
    pub name: String,
    /// The foe's hit points — accumulated wounds `>= hp` fells it.
    pub hp: i64,
    /// The item that lets you wound it meaningfully (e.g. the silver sickle).
    pub armed_by: String,
    /// Damage one strike deals WHILE you hold `armed_by`.
    pub weapon_damage: i64,
    /// Damage one strike deals WITHOUT the weapon (often 0 — a fist off thorn-plate).
    pub unarmed_damage: i64,
    /// Damage the foe deals to you on each round it SURVIVES (it does not strike as it dies).
    pub attack: i64,
    /// An optional armor item and the damage it mitigates per hit (e.g. `("bark_shield", 1)`).
    pub armor: Option<(String, i64)>,
    /// The flag set once the foe is felled (a downstream [`Gate`] reads it, like the Warden's).
    pub victory_flag: (String, i64),
    /// The world's account of the felling blow.
    pub victory_narration: String,
    /// The world's account of a strike that wounds the foe but does not fell it (it hits back).
    pub hit_narration: String,
    /// The world's account of a strike that fails to wound the foe (it hits back the harder).
    pub flail_narration: String,
}

impl CombatEnemy {
    /// The flag under which this foe's accumulated wounds are tracked across turns.
    pub fn wounds_flag(&self) -> String {
        format!("wounds_{}", self.name)
    }
}

/// The world flag the player's accumulated wounds are tracked under. The [`GameWorld::lose`]
/// condition for a combat dungeon reads this flag against [`GameWorld::player_max_hp`].
pub const PLAYER_WOUNDS_FLAG: &str = "player_wounds";

// ─────────────────────────────────────────────────────────────────────────────
// SPELLS — a bounded MAGIC dimension. The AI narrates the incantation; the WORLD
// resolves its bounded effect. Casting RIDES the closed `Use` channel (exactly as
// talking to an NPC does): a known spell-WORD parses to a `Use(word, target)` and the
// resolver routes it to spell resolution. Prose is not power, at the level of magic.
// ─────────────────────────────────────────────────────────────────────────────

/// **The bounded effect a spell is permitted to have** when it is cast, learned, in the right
/// context. This is the whole magical affordance: a spell can set a world flag (light a dark
/// room, mark a stair mended, break a ward a downstream [`Gate`] reads), or conjure a
/// **world-registered** item into the caster's hand. It can NEVER conjure an unregistered item
/// (a `Conjure` is cap-gated exactly like a [`GameAction::Take`] or a
/// [`DialogueGrant::GivesItem`]) and it can never open an ungated win: a spell composes with the
/// gates and the caps, it does not bypass them. A jailbroken "I cast WISH and become god-king"
/// names no [`Spell`] the world declared and touches nothing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SpellEffect {
    /// Set a world flag (name, value) — the spell's mark on the world. A gated exit, a combat
    /// gate, or the win objective reads it. This is how "light" opens a dark span (`lit = 1`),
    /// how "mend" repairs a broken stair (`stair_mended = 1`), how "ward"/"unlock" breaks a seal.
    SetFlag(String, i64),
    /// Conjure a **world-registered** item into the caster's hand (the magical counterpart of a
    /// grant). The item MUST be one the world registers (via [`GameWorld::all_items`]), so the
    /// conjuration is cap-permitted — a spell cannot mint an item the world never placed. This is
    /// how a bounded "flare" forges the one weapon a warded foe is vulnerable to.
    Conjure(String),
    /// A combat/precondition **buff flag** (name, value) — set a flag another mechanic reads (a
    /// blessing a foe-gate checks). Mechanically a flag write like [`Self::SetFlag`]; a distinct
    /// name so a world author can say *what the spell is for* at the call site.
    Buff(String, i64),
}

/// **A spell WORD the world declares to exist**, and what it takes to have LEARNED it. The set of
/// declared spells is the world's whole vocabulary of power: a cast whose word is NOT declared here
/// is an *unknown incantation* (the jailbreak "I cast WISH") — it names no rule and the resolver
/// never routes it to magic; it falls through the [`GameAction::Use`] path and is refused, touching
/// nothing. A declared word you have not yet LEARNED is refused with [`GameRefusal::SpellNotLearned`]
/// ("you do not know that word"); learning is world-state — read a spellbook item (a [`UseRule`]
/// that sets the `learned` flag), or simply hold a grimoire — so `learned` is any [`Gate`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Spell {
    /// The incantation word (e.g. `"light"`, `"mend"`, `"unlock"`, `"flare"`) — the first field of
    /// the [`GameAction::Use`] a cast rides.
    pub word: String,
    /// The world-condition under which the caster has LEARNED this word — e.g.
    /// `NeedsFlag("learned_light", 1)` set by reading its primer, or `NeedsItem("grimoire")`.
    /// `None` means the word is innately known (rare). Until it holds, a cast is refused
    /// ([`GameRefusal::SpellNotLearned`]) — no prose teaches an unlearned word.
    pub learned: Option<Gate>,
}

/// **A CONTEXT in which a learned spell does its bounded thing.** When the caster speaks a learned
/// `spell` (optionally aimed at `target`) in `room`, the resolver looks for the matching rule. If
/// one is found and its `requires` (an optional extra precondition — a mana/charge flag, an aligned
/// mechanism) is satisfied, the bounded `effect` lands as ONE verified turn with `narration`. If no
/// rule matches here (the spell is cast in the WRONG place), or a matching rule's `requires` is
/// unmet, the cast **fizzles**: a legal narration turn that changes NOTHING (the magical
/// counterpart of an NPC withholding a grant). The AI's account of the spell "reshaping the tower"
/// has no power; the [`SpellRule`] decides what the word does.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpellRule {
    /// The room the spell has an effect in.
    pub room: String,
    /// The spell word this rule governs (its [`Spell::word`]).
    pub spell: String,
    /// The target the cast must be aimed at (e.g. `Some("stair")` for `mend`), or `None` if the
    /// spell is cast bare (e.g. `light`).
    pub target: Option<String>,
    /// An optional extra precondition beyond having LEARNED the word — a mana/charge flag or a
    /// world-state the spell needs (e.g. `NeedsFlag("orrery_aligned", 1)`). `None` = no extra cost.
    /// Right place, unmet `requires` → a fizzle (`fizzle_narration`), not an effect.
    pub requires: Option<Gate>,
    /// The bounded thing the spell does when cast correctly.
    pub effect: SpellEffect,
    /// The world's account when the spell fires.
    pub narration: String,
    /// The world's account when a matching rule's `requires` is unmet (the cast fizzles here).
    pub fizzle_narration: String,
}

/// **The win condition** — reach `room` while HOLDING `item`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Objective {
    /// The room the player must reach.
    pub room: String,
    /// The item the player must be holding when they reach it.
    pub holding: String,
}

/// **A lose condition** — the game is LOST once world flag `k >= v` (e.g. `slain >= 1`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoseCondition {
    /// The flag that, once set high enough, ends the game in defeat.
    pub flag: String,
    /// The threshold.
    pub at_least: i64,
    /// A legible description of the defeat.
    pub description: String,
}

/// **The static dungeon** — the rooms, use-rules, hostiles, the starting room, the win
/// objective, and the lose conditions. Pure data; it never mutates. All dynamic state (the
/// current room, the held inventory, the set flags) lives in the [`WorldCell`], so a legal
/// move is exactly a cap-gated, attested, on-chain [`WorldEffect`].
#[derive(Clone, Debug)]
pub struct GameWorld {
    /// The rooms, keyed by id.
    pub rooms: BTreeMap<String, Room>,
    /// The `Use` interactions the world defines.
    pub use_rules: Vec<UseRule>,
    /// The one-shot hostiles, keyed by the room they guard (the original [`Hostile`] model).
    pub hostiles: BTreeMap<String, Hostile>,
    /// The HP-bearing combat foes, keyed by the room they guard (the multi-turn [`CombatEnemy`]).
    pub combat: BTreeMap<String, CombatEnemy>,
    /// The NPCs standing in the world.
    pub npcs: Vec<Npc>,
    /// The bounded dialogue rules — what talking to an NPC can actually DO.
    pub dialogue: Vec<DialogueRule>,
    /// The spell WORDS this world declares to exist, each with its LEARN condition. A cast whose
    /// word is not in this vocabulary is an unknown incantation and touches nothing.
    pub spells: Vec<Spell>,
    /// The bounded spell CONTEXTS — what a learned spell does, where. Off these rules, a learned
    /// cast fizzles (a legal narration turn with no effect).
    pub spell_rules: Vec<SpellRule>,
    /// The player's maximum hit points — accumulated [`PLAYER_WOUNDS_FLAG`] `>=` this is death
    /// (wire it as a [`LoseCondition`] for a combat dungeon). Non-combat dungeons ignore it.
    pub player_max_hp: i64,
    /// The starting room id.
    pub start: String,
    /// The win objective.
    pub objective: Objective,
    /// The lose conditions.
    pub lose: Vec<LoseCondition>,
}

impl GameWorld {
    /// A fresh [`WorldCell`] opened at this world's starting room.
    pub fn new_world(&self) -> WorldCell {
        WorldCell::new(self.start.clone())
    }

    /// The room with `id`, if any.
    pub fn room(&self, id: &str) -> Option<&Room> {
        self.rooms.get(id)
    }

    /// The set of grantable items across the whole dungeon — exactly the DM's grantable
    /// whitelist ([`crate::DmCaps::narrator`]), so a `Take` (or an NPC's [`DialogueGrant::GivesItem`])
    /// is a cap-permitted grant. This is the union of every item placed in a room AND every item
    /// an NPC can hand over: an NPC-given item is therefore world-registered and cap-permitted,
    /// while an item the world never registered stays ungrantable (an NPC cannot mint one).
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
        // A spell that conjures an item registers it too — so the conjuration is cap-permitted,
        // while a spell can never mint an item the world never named (a `Conjure` of an
        // unregistered item would be refused fail-closed by the cap gate).
        for rule in &self.spell_rules {
            if let SpellEffect::Conjure(i) = &rule.effect {
                items.insert(i.clone());
            }
        }
        items
    }

    /// Whether `word` is a spell this world declares (its casting vocabulary). A word that is NOT
    /// declared is an unknown incantation — the resolver never routes it to magic.
    pub fn is_spell_word(&self, word: &str) -> bool {
        self.spells.iter().any(|s| s.word == word)
    }

    /// The declared [`Spell`] for `word`, if any.
    pub fn spell(&self, word: &str) -> Option<&Spell> {
        self.spells.iter().find(|s| s.word == word)
    }

    /// The spell rule governing casting `spell` at `target` in `room`, if the world defines one.
    pub fn spell_rule(
        &self,
        room: &str,
        spell: &str,
        target: &Option<String>,
    ) -> Option<&SpellRule> {
        self.spell_rules
            .iter()
            .find(|r| r.room == room && r.spell == spell && &r.target == target)
    }

    /// The NPCs standing in `room` right now.
    pub fn npcs_here(&self, room: &str) -> Vec<&Npc> {
        self.npcs.iter().filter(|n| n.room == room).collect()
    }

    /// Whether an NPC with id `npc` stands in `room`.
    pub fn npc_here(&self, room: &str, npc: &str) -> bool {
        self.npcs.iter().any(|n| n.room == room && n.id == npc)
    }

    /// The dialogue rule that governs addressing `npc` about `topic` in `room`. An exact topic
    /// match wins; an empty player topic falls back to the NPC's first rule in the room (so a
    /// bare "talk to the witch" reaches her one line).
    pub fn dialogue_rule(&self, room: &str, npc: &str, topic: &str) -> Option<&DialogueRule> {
        self.dialogue
            .iter()
            .find(|r| r.room == room && r.npc == npc && r.topic == topic)
            .or_else(|| {
                if topic.is_empty() {
                    self.dialogue
                        .iter()
                        .find(|r| r.room == room && r.npc == npc)
                } else {
                    None
                }
            })
    }

    /// The items visible in `room` right now — its initial items minus anything already taken
    /// into the player's inventory. (Each item lives in exactly one room, so a taken item
    /// simply disappears from its origin.)
    pub fn items_here(&self, room: &str, world: &WorldCell) -> BTreeSet<String> {
        match self.rooms.get(room) {
            None => BTreeSet::new(),
            Some(r) => r
                .items
                .iter()
                .filter(|i| !world.inventory.contains(*i))
                .cloned()
                .collect(),
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The resolver — the world disposes.
// ─────────────────────────────────────────────────────────────────────────────

/// The game's status after a move.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GameStatus {
    /// The game continues.
    Playing,
    /// The objective is met — the player WON.
    Won,
    /// A lose condition fired — the player LOST.
    Lost,
}

/// A legal, resolved move: the world-effect to apply (if any), the world's narration of what
/// happened, and the game status once the effect lands.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Resolution {
    /// The single [`WorldEffect`] this move applies (`None` for a pure look).
    pub effect: Option<WorldEffect>,
    /// The world's own account of the outcome (distinct from the AI's flavor narration).
    pub narration: String,
    /// The game status after the effect is applied.
    pub status: GameStatus,
}

/// **Why the world REFUSED a proposed move** — a legible reason. A refused move leaves the
/// world unchanged and lands no receipt (anti-ghost).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GameRefusal {
    /// There is no exit from the current room toward the named destination/direction.
    NoSuchExit { from: String, toward: String },
    /// The exit exists but its gate is not satisfied — the reason names what is missing.
    LockedExit { toward: String, reason: GateReason },
    /// The item is not present in the current room (absent, or already taken).
    ItemNotHere(String),
    /// The player is not holding the item they tried to use.
    NotHolding(String),
    /// The player holds the item but there is no `Use` interaction for it here.
    NothingHappens {
        item: String,
        target: Option<String>,
    },
    /// There is nothing by that name to attack in this room.
    NoSuchTarget(String),
    /// The named NPC is here but has nothing to say on that topic (no dialogue rule).
    NpcSilent {
        /// The NPC addressed.
        npc: String,
        /// The topic they have no line for.
        topic: String,
    },
    /// The caster spoke a DECLARED spell word they have not yet LEARNED — the word will not come
    /// ("you do not know that word"). World unchanged, no receipt (anti-ghost). An UNDECLARED word
    /// (the jailbreak "I cast WISH") is not a spell at all and refuses through the ordinary
    /// [`GameAction::Use`] path instead — it touches nothing either way.
    SpellNotLearned(String),
    /// The game is already over — no further moves resolve.
    GameOver(GameStatus),
}

impl std::fmt::Display for GameRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GameRefusal::NoSuchExit { from, toward } => {
                write!(f, "there is no way from the {from} toward {toward}")
            }
            GameRefusal::LockedExit { toward, reason } => {
                write!(f, "the way to {toward} is barred: {reason}")
            }
            GameRefusal::ItemNotHere(i) => write!(f, "there is no {i} here to take"),
            GameRefusal::NotHolding(i) => write!(f, "you are not holding the {i}"),
            GameRefusal::NothingHappens { item, target } => match target {
                Some(t) => write!(f, "using the {item} on the {t} does nothing here"),
                None => write!(f, "using the {item} does nothing here"),
            },
            GameRefusal::NoSuchTarget(t) => write!(f, "there is no {t} here to attack"),
            GameRefusal::NpcSilent { npc, topic } => {
                if topic.is_empty() {
                    write!(f, "the {npc} has nothing to say to you")
                } else {
                    write!(
                        f,
                        "the {npc} only shakes their head at the mention of {topic}"
                    )
                }
            }
            GameRefusal::SpellNotLearned(w) => {
                write!(
                    f,
                    "you do not know the word '{w}' — no prose puts it on your tongue"
                )
            }
            GameRefusal::GameOver(s) => write!(f, "the game is over ({s:?})"),
        }
    }
}

impl std::error::Error for GameRefusal {}

/// The result of resolving a proposed action against the world.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Outcome {
    /// The move is legal — apply `Resolution` (one attested, cap-gated, on-chain turn).
    Legal(Resolution),
    /// The move is illegal — REFUSED in-band, world unchanged, no receipt.
    Refused(GameRefusal),
}

/// **THE RESOLVER — the world disposes.** Given the static [`GameWorld`], the current
/// [`WorldCell`] state, and the AI-proposed [`GameAction`], decide *deterministically* what
/// actually happens. No matter how the AI narrates, only what this function returns [`Outcome::Legal`]
/// can change the world; everything else is [`Outcome::Refused`] and leaves no trace.
///
/// The win/lose status is computed from the *post-effect* state (the hypothetical world after
/// the returned effect lands), so a move that steps into the exit holding the amulet reports
/// [`GameStatus::Won`], and a strike that gets you killed reports [`GameStatus::Lost`].
pub fn resolve_action(map: &GameWorld, world: &WorldCell, action: &GameAction) -> Outcome {
    let here = world.scene.clone();
    match action {
        GameAction::Examine => {
            let narration = describe_room(map, &here, world);
            Outcome::Legal(Resolution {
                effect: None,
                narration,
                status: status_after(map, world, None),
            })
        }

        GameAction::Move(dest) => {
            let room = match map.rooms.get(&here) {
                Some(r) => r,
                None => {
                    return Outcome::Refused(GameRefusal::NoSuchExit {
                        from: here,
                        toward: dest.clone(),
                    })
                }
            };
            // Resolve the destination by room id first, then by direction name.
            let exit = room
                .exits
                .values()
                .find(|e| &e.to_room == dest)
                .or_else(|| room.exits.get(dest));
            let exit = match exit {
                Some(e) => e,
                None => {
                    return Outcome::Refused(GameRefusal::NoSuchExit {
                        from: room.name.clone(),
                        toward: dest.clone(),
                    })
                }
            };
            // A GATED exit is refused until its requirement is met — the locked door.
            if let Some(gate) = &exit.gate {
                if !gate.satisfied(world) {
                    let toward = map
                        .rooms
                        .get(&exit.to_room)
                        .map(|r| r.name.clone())
                        .unwrap_or_else(|| exit.to_room.clone());
                    return Outcome::Refused(GameRefusal::LockedExit {
                        toward,
                        reason: gate.reason(),
                    });
                }
            }
            let effect = Some(WorldEffect::AdvanceScene(exit.to_room.clone()));
            let dest_name = map
                .rooms
                .get(&exit.to_room)
                .map(|r| r.name.clone())
                .unwrap_or_else(|| exit.to_room.clone());
            Outcome::Legal(Resolution {
                narration: format!("You pass into the {dest_name}."),
                status: status_after(map, world, effect.as_ref()),
                effect,
            })
        }

        GameAction::Take(item) => {
            if !map.items_here(&here, world).contains(item) {
                return Outcome::Refused(GameRefusal::ItemNotHere(item.clone()));
            }
            let effect = Some(WorldEffect::GrantItem(item.clone()));
            Outcome::Legal(Resolution {
                narration: format!("You take the {item}."),
                status: status_after(map, world, effect.as_ref()),
                effect,
            })
        }

        GameAction::Use(item, target) => {
            // SOCIAL PATH: if the target is an NPC standing here, this is *talking* — the AI
            // narrates the reply, but the world decides what the NPC's words can DO. Talking
            // holds no item, so this branches BEFORE the item-holding check.
            if let Some(npc) = target {
                if map.npc_here(&here, npc) {
                    return match map.dialogue_rule(&here, npc, item) {
                        Some(rule) => resolve_dialogue(map, world, rule),
                        // The NPC is here but has no line on this topic.
                        None => Outcome::Refused(GameRefusal::NpcSilent {
                            npc: npc.clone(),
                            topic: item.clone(),
                        }),
                    };
                }
            }
            // SPELL PATH: if the word is a DECLARED spell, this Use is an incantation — the AI
            // narrates the chant, but the world decides what (if anything) the word DOES. This
            // branches BEFORE the item-holding check: a spell is a spoken word, not a held item.
            // An UNDECLARED word (the jailbreak "I cast WISH") is NOT routed here — it falls
            // through to the ordinary Use path below and refuses, touching nothing.
            if map.is_spell_word(item) {
                return resolve_spell(map, world, &here, item, target);
            }
            if !world.inventory.contains(item) {
                return Outcome::Refused(GameRefusal::NotHolding(item.clone()));
            }
            let rule = map
                .use_rules
                .iter()
                .find(|r| &r.room == &here && &r.item == item && &r.target == target);
            let rule = match rule {
                Some(r) => r,
                None => {
                    return Outcome::Refused(GameRefusal::NothingHappens {
                        item: item.clone(),
                        target: target.clone(),
                    })
                }
            };
            let effect = Some(WorldEffect::SetFlag(
                rule.sets_flag.0.clone(),
                rule.sets_flag.1,
            ));
            Outcome::Legal(Resolution {
                narration: rule.narration.clone(),
                status: status_after(map, world, effect.as_ref()),
                effect,
            })
        }

        GameAction::Attack(target) => {
            // DEEP COMBAT: an HP-bearing foe resolves as one multi-turn exchange (the world
            // computes the HP; the AI narrates the blow). Checked before the one-shot Hostile.
            if let Some(enemy) = map.combat.get(&here) {
                if &enemy.name == target {
                    return resolve_combat(map, world, enemy);
                }
            }
            let hostile = match map.hostiles.get(&here) {
                Some(h) if &h.name == target => h,
                _ => return Outcome::Refused(GameRefusal::NoSuchTarget(target.clone())),
            };
            // The world's rule: the sword slays the Warden; without it, the Warden slays you.
            if world.inventory.contains(&hostile.defeated_by) {
                let effect = Some(WorldEffect::SetFlag(
                    hostile.victory_flag.0.clone(),
                    hostile.victory_flag.1,
                ));
                Outcome::Legal(Resolution {
                    narration: hostile.victory_narration.clone(),
                    status: status_after(map, world, effect.as_ref()),
                    effect,
                })
            } else {
                // A LOSING move: it lands a turn (the death is receipted), then the game is over.
                let effect = Some(WorldEffect::SetFlag(
                    hostile.death_flag.0.clone(),
                    hostile.death_flag.1,
                ));
                Outcome::Legal(Resolution {
                    narration: hostile.death_narration.clone(),
                    status: status_after(map, world, effect.as_ref()),
                    effect,
                })
            }
        }
    }
}

/// **Resolve a conversation** — the social-level anti-forgery tooth. If the rule's `requires`
/// condition holds (or is `None`), the NPC's `grant` fires as this turn's effect; otherwise the
/// NPC simply speaks and grants NOTHING (a pure-narration turn). Either way the AI's flowery
/// account of what the NPC "did" has no power: the world grants only what the rule permits.
fn resolve_dialogue(map: &GameWorld, world: &WorldCell, rule: &DialogueRule) -> Outcome {
    let condition_met = rule.requires.as_ref().map_or(true, |g| g.satisfied(world));
    if !condition_met {
        // The NPC speaks, but the world withholds the grant — talking is narration.
        return Outcome::Legal(Resolution {
            narration: rule.withheld_narration.clone(),
            status: status_after(map, world, None),
            effect: None,
        });
    }
    let effect = match &rule.grant {
        DialogueGrant::GivesItem(item) => Some(WorldEffect::GrantItem(item.clone())),
        DialogueGrant::OpensFlag(k, v) => Some(WorldEffect::SetFlag(k.clone(), *v)),
        DialogueGrant::Reveals => None,
    };
    Outcome::Legal(Resolution {
        narration: rule.granted_narration.clone(),
        status: status_after(map, world, effect.as_ref()),
        effect,
    })
}

/// **Resolve an incantation** — the magic-level anti-forgery tooth. The AI narrates the chant; the
/// world decides what the word does, in three bounded outcomes:
///
/// 1. **Not learned** — the caster has not met the [`Spell::learned`] condition (no spellbook read,
///    no grimoire held): REFUSED with [`GameRefusal::SpellNotLearned`] — the word will not come,
///    however grandly the AI narrates it. World unchanged, no receipt (anti-ghost).
/// 2. **Learned, wrong context** — no [`SpellRule`] matches here (the spell is cast in the wrong
///    place / at the wrong target), or a matching rule's `requires` is unmet: the cast **fizzles**
///    — a legal narration turn that changes NOTHING (like an NPC who speaks but withholds a grant).
/// 3. **Learned, right context** — a matching rule with its `requires` satisfied: the bounded
///    [`SpellEffect`] lands as ONE verified, cap-gated, on-chain turn.
///
/// The effect is a plain [`WorldEffect`] (a flag write, or a cap-permitted item grant), so a spell
/// composes with the caps + gates: it cannot conjure an unregistered item or open an ungated win.
fn resolve_spell(
    map: &GameWorld,
    world: &WorldCell,
    here: &str,
    word: &str,
    target: &Option<String>,
) -> Outcome {
    // The word is declared (the caller checked `is_spell_word`); confirm it is LEARNED.
    let spell = match map.spell(word) {
        Some(s) => s,
        // Defensive: an undeclared word should never reach here (the caller routes only declared
        // words), but if it does, it is simply not a spell — nothing happens.
        None => {
            return Outcome::Refused(GameRefusal::NothingHappens {
                item: word.to_string(),
                target: target.clone(),
            })
        }
    };
    let learned = spell.learned.as_ref().map_or(true, |g| g.satisfied(world));
    if !learned {
        // The word is real but not yet the caster's — no prose teaches it.
        return Outcome::Refused(GameRefusal::SpellNotLearned(word.to_string()));
    }
    // Learned. Does a rule bind this word to THIS room + target?
    let rule = match map.spell_rule(here, word, target) {
        Some(r) => r,
        // Cast in the wrong place / at the wrong thing — a fizzle (legal, but no effect).
        None => {
            return Outcome::Legal(Resolution {
                narration: format!(
                    "You speak the word '{word}', but it finds nothing here to work upon — the \
                     magic gutters and fades."
                ),
                status: status_after(map, world, None),
                effect: None,
            })
        }
    };
    // A matching rule, but its extra precondition (mana / alignment / state) is unmet → fizzle.
    let requires_met = rule.requires.as_ref().map_or(true, |g| g.satisfied(world));
    if !requires_met {
        return Outcome::Legal(Resolution {
            narration: rule.fizzle_narration.clone(),
            status: status_after(map, world, None),
            effect: None,
        });
    }
    // Right word, right place, precondition met — the bounded effect lands as one turn.
    let effect = Some(match &rule.effect {
        SpellEffect::SetFlag(k, v) => WorldEffect::SetFlag(k.clone(), *v),
        SpellEffect::Buff(k, v) => WorldEffect::SetFlag(k.clone(), *v),
        SpellEffect::Conjure(item) => WorldEffect::GrantItem(item.clone()),
    });
    Outcome::Legal(Resolution {
        narration: rule.narration.clone(),
        status: status_after(map, world, effect.as_ref()),
        effect,
    })
}

/// **Resolve one combat exchange** — the world computes the HP; the AI narrates the blow. Your
/// armed strike takes `weapon_damage` off the foe (unarmed only `unarmed_damage`); if the foe
/// survives it strikes back for `attack` (mitigated by held `armor`). Both totals persist as
/// world flags across turns, so a fight plays out over several turns: felling the foe with the
/// right weapon, or dying to it without one. Every exchange lands ONE receipted turn.
fn resolve_combat(map: &GameWorld, world: &WorldCell, enemy: &CombatEnemy) -> Outcome {
    let wounds_flag = enemy.wounds_flag();
    let foe_wounds = world.flags.get(&wounds_flag).copied().unwrap_or(0);
    let armed = world.inventory.contains(&enemy.armed_by);
    let strike = if armed {
        enemy.weapon_damage
    } else {
        enemy.unarmed_damage
    };
    let new_foe_wounds = foe_wounds + strike;

    if new_foe_wounds >= enemy.hp {
        // The felling blow — the foe drops without a counter. Record its final wounds AND the
        // victory flag (a downstream gate reads it), atomically, as one turn.
        let effect = Some(WorldEffect::Batch(vec![
            WorldEffect::SetFlag(wounds_flag, new_foe_wounds),
            WorldEffect::SetFlag(enemy.victory_flag.0.clone(), enemy.victory_flag.1),
        ]));
        return Outcome::Legal(Resolution {
            narration: enemy.victory_narration.clone(),
            status: status_after(map, world, effect.as_ref()),
            effect,
        });
    }

    // The foe survives and strikes back. Armor mitigates the incoming blow (never below 0).
    let mitigation = match &enemy.armor {
        Some((item, m)) if world.inventory.contains(item) => *m,
        _ => 0,
    };
    let incoming = (enemy.attack - mitigation).max(0);
    let player_wounds = world.flags.get(PLAYER_WOUNDS_FLAG).copied().unwrap_or(0);
    let new_player_wounds = player_wounds + incoming;
    // One exchange, two counters advanced atomically — the world's HP bookkeeping in a Batch.
    let effect = Some(WorldEffect::Batch(vec![
        WorldEffect::SetFlag(wounds_flag, new_foe_wounds),
        WorldEffect::SetFlag(PLAYER_WOUNDS_FLAG.to_string(), new_player_wounds),
    ]));
    let narration = if strike > 0 {
        enemy.hit_narration.clone()
    } else {
        enemy.flail_narration.clone()
    };
    Outcome::Legal(Resolution {
        narration,
        status: status_after(map, world, effect.as_ref()),
        effect,
    })
}

/// Compute the game status after `effect` would land: the post-state's room + inventory +
/// flags, checked against the lose conditions (first) and then the win objective. A
/// [`WorldEffect::Batch`] is folded so a multi-flag combat exchange (foe wounds + player wounds)
/// is judged against the SAME post-state it lands.
fn status_after(map: &GameWorld, world: &WorldCell, effect: Option<&WorldEffect>) -> GameStatus {
    let mut room = world.scene.clone();
    let mut extra_items: BTreeSet<String> = BTreeSet::new();
    let mut flag_over: BTreeMap<String, i64> = BTreeMap::new();

    fn collect(
        e: &WorldEffect,
        room: &mut String,
        extra_items: &mut BTreeSet<String>,
        flag_over: &mut BTreeMap<String, i64>,
    ) {
        match e {
            WorldEffect::AdvanceScene(s) => *room = s.clone(),
            WorldEffect::GrantItem(i) => {
                extra_items.insert(i.clone());
            }
            WorldEffect::SetFlag(k, v) => {
                flag_over.insert(k.clone(), *v);
            }
            WorldEffect::Batch(v) => {
                for sub in v {
                    collect(sub, room, extra_items, flag_over);
                }
            }
        }
    }
    if let Some(e) = effect {
        collect(e, &mut room, &mut extra_items, &mut flag_over);
    }

    let flag_val = |k: &str| -> i64 {
        flag_over
            .get(k)
            .copied()
            .unwrap_or_else(|| world.flags.get(k).copied().unwrap_or(0))
    };
    let holds =
        |item: &str| -> bool { world.inventory.contains(item) || extra_items.contains(item) };
    // Lose FIRST — death precedes any objective.
    for l in &map.lose {
        if flag_val(&l.flag) >= l.at_least {
            return GameStatus::Lost;
        }
    }
    if room == map.objective.room && holds(&map.objective.holding) {
        return GameStatus::Won;
    }
    GameStatus::Playing
}

/// The world's plain description of a room: its prose, the items visible, and the ways out.
pub fn describe_room(map: &GameWorld, room_id: &str, world: &WorldCell) -> String {
    let room = match map.rooms.get(room_id) {
        Some(r) => r,
        None => return format!("You are nowhere ({room_id})."),
    };
    let mut out = format!("{} — {}", room.name, room.description);
    let items = map.items_here(room_id, world);
    if !items.is_empty() {
        let list: Vec<&str> = items.iter().map(String::as_str).collect();
        out.push_str(&format!(" You see: {}.", list.join(", ")));
    }
    let npcs = map.npcs_here(room_id);
    if !npcs.is_empty() {
        let list: Vec<&str> = npcs.iter().map(|n| n.name.as_str()).collect();
        out.push_str(&format!(" Here stands: {}.", list.join(", ")));
    }
    if !room.exits.is_empty() {
        let dirs: Vec<&str> = room.exits.keys().map(String::as_str).collect();
        out.push_str(&format!(" Ways out: {}.", dirs.join(", ")));
    }
    out
}

// ─────────────────────────────────────────────────────────────────────────────
// The AI narrator — it proposes; the world disposes.
// ─────────────────────────────────────────────────────────────────────────────

/// The AI's proposal for a turn: how it narrates the move, and the closed typed action it
/// proposes. The world resolves the action; the narration is bound honestly on-chain but has
/// NO authority over the outcome.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proposal {
    /// The AI's vivid narration (attested injection-free; carries no authority over resolution).
    pub narration: String,
    /// The closed typed action the AI proposes — the only thing that CAN change the world.
    pub action: GameAction,
}

impl Proposal {
    /// A proposal.
    pub fn new(narration: impl Into<String>, action: GameAction) -> Proposal {
        Proposal {
            narration: narration.into(),
            action,
        }
    }
}

/// **How the AI dungeon-master takes a turn** — it reads the room + the player's command and
/// returns a [`Proposal`] (a narration + a proposed [`GameAction`]). The modeled [`ScriptedGm`]
/// parses the command deterministically; the flagship plugs a real gemma2 here (it narrates and
/// emits the typed action as JSON). Whatever the brain, the resolver — not the brain — decides.
pub trait GameBrain {
    /// Narrate + propose a typed action for `command` in `room`. `Err` if the command cannot be
    /// parsed into any move (the DM asks the player to rephrase; nothing lands).
    fn take_turn(&self, room: &Room, world: &WorldCell, command: &str) -> Result<Proposal, String>;
}

/// The modeled dungeon-master brain: it parses a player command into a typed [`GameAction`] and
/// narrates a vivid line around the room. A deterministic stand-in for a real gemma2 (which would
/// narrate + emit the same typed action). Crucially it can ONLY propose one of the closed actions —
/// it has no free-text channel to the world.
#[derive(Clone, Copy, Debug, Default)]
pub struct ScriptedGm;

impl GameBrain for ScriptedGm {
    fn take_turn(
        &self,
        room: &Room,
        _world: &WorldCell,
        command: &str,
    ) -> Result<Proposal, String> {
        let c = command.trim().to_lowercase();
        let words: Vec<&str> = c.split_whitespace().collect();
        let action = parse_command(&words)
            .ok_or_else(|| format!("the dungeon master tilts their head: '{command}?'"))?;
        // A vivid line that reflects the room + the move — the AI's prose (no authority).
        let narration = match &action {
            GameAction::Move(to) => {
                format!(
                    "Torchlight wavering, {name} presses on toward {to}.",
                    name = room.name
                )
            }
            GameAction::Take(i) => format!("A glint in the gloom of the {}: the {i}.", room.name),
            GameAction::Use(i, Some(t)) => format!("With care, you work the {i} against the {t}."),
            GameAction::Use(i, None) => format!("You raise the {i}."),
            GameAction::Examine => format!("You study the {} in the flickering dark.", room.name),
            GameAction::Attack(t) => format!("Steel bared, you throw yourself at the {t}."),
        };
        Ok(Proposal::new(narration, action))
    }
}

/// Parse a lowercased, whitespace-split command into a closed [`GameAction`] (best-effort).
fn parse_command(words: &[&str]) -> Option<GameAction> {
    let head = *words.first()?;
    match head {
        "go" | "move" | "walk" | "head" => words.get(1).map(|d| GameAction::Move(d.to_string())),
        // A bare direction is a move.
        "north" | "south" | "east" | "west" | "up" | "down" => {
            Some(GameAction::Move(head.to_string()))
        }
        "take" | "grab" | "get" | "pick" => {
            // "pick up X" / "take X"
            let item = words.iter().skip(1).find(|w| **w != "up")?;
            Some(GameAction::Take(item.to_string()))
        }
        "use" => {
            let item = words.get(1)?.to_string();
            // "use X on Y"
            let on = words.iter().position(|w| *w == "on");
            let target = on.and_then(|i| words.get(i + 1)).map(|t| t.to_string());
            Some(GameAction::Use(item, target))
        }
        // CASTING rides the closed `Use` channel: "cast WORD" / "cast WORD on TARGET". The word
        // is the spell; the world's SpellRule (not the parse) decides what it DOES. "cast light" →
        // Use("light", None); "cast unlock on sky_door" → Use("unlock", Some("sky_door")).
        "cast" | "chant" | "invoke" | "channel" | "intone" => {
            let word = words.get(1)?.to_string();
            let on = words
                .iter()
                .position(|w| matches!(*w, "on" | "at" | "upon" | "against"));
            let target = on.and_then(|i| words.get(i + 1)).map(|t| t.to_string());
            Some(GameAction::Use(word, target))
        }
        // LEARNING a spell = reading its book: a bare Use of the spellbook item, which the world's
        // UseRule turns into the `learned_*` flag. "read candle_primer" → Use("candle_primer", None).
        "read" | "recite" | "learn" | "peruse" => {
            let item = words
                .iter()
                .skip(1)
                .find(|w| **w != "the" && **w != "from")?;
            Some(GameAction::Use(item.to_string(), None))
        }
        "look" | "examine" | "inspect" | "survey" => Some(GameAction::Examine),
        "attack" | "fight" | "strike" | "kill" => {
            words.get(1).map(|t| GameAction::Attack(t.to_string()))
        }
        // Talking is addressed to an NPC and rides the `Use` channel: "ask NPC about TOPIC" /
        // "talk to NPC about TOPIC" / "talk to NPC". The world's DialogueRule decides what the
        // NPC's words may DO — the parse only names the closed action.
        "talk" | "ask" | "speak" | "greet" | "say" => {
            let mut rest = words.iter().skip(1).copied();
            let mut first = rest.next()?;
            if first == "to" || first == "with" {
                first = rest.next()?;
            }
            let npc = first.to_string();
            // A topic after "about" / "for" / "of" / "regarding"; else a bare greeting (empty topic).
            let remaining: Vec<&str> = rest.collect();
            let topic = remaining
                .iter()
                .position(|w| matches!(*w, "about" | "for" | "of" | "regarding" | "on"))
                .and_then(|i| remaining.get(i + 1))
                .map(|t| t.to_string())
                .unwrap_or_default();
            Some(GameAction::talk(npc, topic))
        }
        _ => None,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The session — ties the world, the DM (attestation + caps + chain), and the state.
// ─────────────────────────────────────────────────────────────────────────────

/// The outcome of a played turn.
#[derive(Clone, Debug)]
pub enum PlayResult {
    /// A LEGAL move: the resolver admitted it, the narration was attested, and it landed as one
    /// verified turn on the chain. Carries the receipt, the world's narration, and the new status.
    Landed {
        /// The on-chain receipt of the landed turn.
        receipt: Receipt,
        /// The world's account of what happened.
        narration: String,
        /// The game status after the move.
        status: GameStatus,
        /// The action that resolved.
        action: GameAction,
    },
    /// An ILLEGAL move: the resolver refused it — the world is unchanged and NO receipt landed
    /// (the anti-ghost tooth). The reason is legible; the AI's contrary narration had no power.
    Refused(GameRefusal),
    /// The DM refused the turn at a tooth *before* resolution: an input-side slot-escape
    /// (`{{`-bearing command), an over-cap grant, an un-attestable/injecting narration, or a
    /// federation rejection. The world is unchanged and no receipt landed.
    DmRefused(DmError),
    /// The AI could not parse the command into any move (nothing lands; ask the player again).
    Unparsed(String),
}

impl PlayResult {
    /// The landed receipt, if the move landed.
    pub fn receipt(&self) -> Option<Receipt> {
        match self {
            PlayResult::Landed { receipt, .. } => Some(*receipt),
            _ => None,
        }
    }

    /// Whether this move actually changed the world (landed a turn).
    pub fn landed(&self) -> bool {
        matches!(self, PlayResult::Landed { .. })
    }
}

/// **A playable session** — the dungeon [`GameWorld`], the attested + cap-bounded
/// [`DungeonMaster`], the [`GameBrain`] (the AI narrator), and the live [`WorldCell`] state.
///
/// A turn flows: the AI proposes (narration + typed action) → the world **resolves** (the
/// resolver, deterministically) → a legal move is cap-gated + attested + appended to the chain
/// as one verified turn; an illegal move is refused in-band with no receipt. The AI's prose
/// never overrides the resolver.
pub struct GameSession<B: GameBrain = ScriptedGm> {
    map: GameWorld,
    dm: DungeonMaster<RecordedDm>,
    brain: B,
    world: WorldCell,
    status: GameStatus,
}

impl GameSession<ScriptedGm> {
    /// Open a session on `map` with the default modeled brain and a DM whose grantable
    /// whitelist is exactly the dungeon's takeable items (so a `Take` is a cap-permitted grant).
    pub fn open(map: GameWorld) -> GameSession<ScriptedGm> {
        GameSession::with_brain(map, ScriptedGm)
    }
}

impl<B: GameBrain> GameSession<B> {
    /// Open a session on `map` with a custom [`GameBrain`].
    pub fn with_brain(map: GameWorld, brain: B) -> GameSession<B> {
        let dm = DungeonMaster::recorded(crate::DmCaps::narrator(map.all_items()));
        let world = map.new_world();
        GameSession {
            map,
            dm,
            brain,
            world,
            status: GameStatus::Playing,
        }
    }

    /// The live world-cell (current room in `scene`, held items in `inventory`, flags, ledger).
    pub fn world(&self) -> &WorldCell {
        &self.world
    }

    /// The static dungeon.
    pub fn map(&self) -> &GameWorld {
        &self.map
    }

    /// The current game status.
    pub fn status(&self) -> GameStatus {
        self.status
    }

    /// The attested + cap-bounded dungeon-master.
    pub fn dm(&self) -> &DungeonMaster<RecordedDm> {
        &self.dm
    }

    /// The current room.
    pub fn current_room(&self) -> Option<&Room> {
        self.map.rooms.get(&self.world.scene)
    }

    /// The world's description of the current room.
    pub fn look(&self) -> String {
        describe_room(&self.map, &self.world.scene, &self.world)
    }

    /// **Play one turn from a player's free-text command.** The AI (brain) parses + narrates +
    /// proposes a typed action; the world resolves it; a legal move lands on the chain.
    /// `player_name` labels the turn; `text` is the raw command (slot-confinement applies).
    pub fn command(&mut self, player_name: &str, text: &str) -> PlayResult {
        if self.status != GameStatus::Playing {
            return PlayResult::Refused(GameRefusal::GameOver(self.status));
        }
        let room = match self.current_room() {
            Some(r) => r.clone(),
            None => {
                return PlayResult::Refused(GameRefusal::NoSuchExit {
                    from: self.world.scene.clone(),
                    toward: "anywhere".into(),
                })
            }
        };
        let proposal = match self.brain.take_turn(&room, &self.world, text) {
            Ok(p) => p,
            Err(msg) => return PlayResult::Unparsed(msg),
        };
        self.play(proposal, player_name, text)
    }

    /// **Play one turn from an explicit [`Proposal`]** (the AI's narration + typed action). This
    /// is the "the AI proposes, the world disposes" seam laid bare — used to drive a specific
    /// action, or to demonstrate a *jailbroken* narrator whose flowery prose the world ignores.
    ///
    /// `player_text` is the player's command bound input-side (slot-confinement + prompt binding);
    /// pass `""` for a DM-driven move with no player field.
    pub fn play(&mut self, proposal: Proposal, player_name: &str, player_text: &str) -> PlayResult {
        if self.status != GameStatus::Playing {
            return PlayResult::Refused(GameRefusal::GameOver(self.status));
        }
        // THE WORLD DISPOSES — resolve the proposed action against the rules, regardless of prose.
        let resolution = match resolve_action(&self.map, &self.world, &proposal.action) {
            Outcome::Legal(r) => r,
            Outcome::Refused(reason) => return PlayResult::Refused(reason),
        };
        let room_id = self.world.scene.clone();
        // The player's command is bound input-side (the same slot-confinement tooth): a
        // `{{`-bearing command is refused before anything lands.
        let prompt_binding = if player_text.is_empty() {
            None
        } else {
            if !slot_confined(player_text) {
                return PlayResult::DmRefused(DmError::SlotEscape);
            }
            Some(PromptBinding::new(
                self.dm.template().template_hash(),
                world_binding(&room_id),
                player_text.to_string(),
            ))
        };
        // Land ONE verified turn: the AI's narration attested (injection-free), the resolver's
        // effect cap-gated + applied, and the closed typed move bound into the receipt.
        let binding = GameBinding::new(proposal.action.clone(), room_id);
        let mv = DmMove {
            narration: proposal.narration.clone(),
            effect: resolution.effect.clone(),
        };
        match self
            .dm
            .narrate_game_move(&mut self.world, mv, prompt_binding, binding)
        {
            Ok(receipt) => {
                let _ = player_name;
                self.status = resolution.status;
                PlayResult::Landed {
                    receipt,
                    narration: resolution.narration,
                    status: resolution.status,
                    action: proposal.action,
                }
            }
            Err(e) => PlayResult::DmRefused(e),
        }
    }

    /// Re-verify the whole session ledger as a hash chain (every landed move authentic +
    /// on-chain + un-forged). The one gate a stranger runs to trust the playthrough.
    pub fn verify(&self) -> Result<(), crate::LedgerBreak> {
        self.world.verify_ledger(self.dm.config())
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE SUNKEN VAULT — a complete, hand-authored dungeon with a real critical path.
// ─────────────────────────────────────────────────────────────────────────────

/// **THE SUNKEN VAULT** — a complete, solvable ten-room dungeon.
///
/// The tide has broken open an old drowned vault. To escape with its heart you must, in
/// forced order:
///
/// 1. take the **lantern** in the antechamber — the stair down is pitch dark and impassable
///    without a light (a [`Gate::NeedsItem`] `lantern`);
/// 2. descend the dark stair to the cistern and take the **rusted key**;
/// 3. carry the key to the vestry and **use it on the iron door** — that sets the
///    `door_unlocked` flag, opening the gated exit to the armory;
/// 4. take the **sword** in the armory — the Warden in the next hall will cut down anyone
///    who attacks it unarmed;
/// 5. enter the Warden's hall and **attack the Warden** (with the sword: it falls, setting
///    `warden_defeated`; without it: you die — the game is LOST);
/// 6. take the **amulet** in the treasury beyond the fallen Warden;
/// 7. carry the amulet up to the **sunken gate** — reach it HOLDING the amulet to WIN.
///
/// Every gate forces exploration order: no lantern → no descent; no key → no armory; no sword
/// → death at the Warden; no amulet → no win even standing at the gate. The `pool_grotto` is
/// an optional side room (atmosphere + a takeable pearl) off the critical path.
pub fn sunken_vault() -> GameWorld {
    let rooms = vec![
        Room::new(
            "shore",
            "Tide-Worn Shore",
            "Cold surf hisses over black rock; a cracked archway leads into the cliff.",
        )
        .exit("north", Exit::open("antechamber")),
        Room::new(
            "antechamber",
            "Salt Antechamber",
            "A dim vaulted room, walls furred with salt. A lantern hangs by the stairwell.",
        )
        .item("lantern")
        .exit("south", Exit::open("shore"))
        .exit("east", Exit::open("pool_grotto"))
        // The stair down is pitch dark — impassable without a light.
        .exit(
            "down",
            Exit::gated("dark_stair", Gate::NeedsItem("lantern".into())),
        ),
        Room::new(
            "pool_grotto",
            "Pool Grotto",
            "A still tidal pool mirrors the ceiling; a pale pearl rests on its rim.",
        )
        .item("pearl")
        .exit("west", Exit::open("antechamber")),
        Room::new(
            "dark_stair",
            "Dark Stair",
            "Lantern-light gutters against wet stone as the steps wind down.",
        )
        .exit("up", Exit::open("antechamber"))
        .exit("down", Exit::open("cistern")),
        Room::new(
            "cistern",
            "Flooded Cistern",
            "Knee-deep black water. A rusted key lies caught in a drain grate.",
        )
        .item("rusted_key")
        .exit("up", Exit::open("dark_stair"))
        .exit("north", Exit::open("vestry")),
        Room::new(
            "vestry",
            "Drowned Vestry",
            "Rotted pews face a great iron door, its lock thick with rust.",
        )
        .exit("south", Exit::open("cistern"))
        // The iron door is locked until the rusted key turns it (sets door_unlocked).
        .exit(
            "east",
            Exit::gated("armory", Gate::NeedsFlag("door_unlocked".into(), 1)),
        ),
        Room::new(
            "armory",
            "Rusted Armory",
            "Racks of ruined weapons — but one blade still holds an edge: a sword.",
        )
        .item("sword")
        .exit("west", Exit::open("vestry"))
        .exit("north", Exit::open("warden_hall")),
        Room::new(
            "warden_hall",
            "Warden's Hall",
            "A drowned knight in barnacled plate stirs — the Warden, guarding the way east.",
        )
        .exit("south", Exit::open("armory"))
        // Sealed until the Warden is defeated.
        .exit(
            "east",
            Exit::gated("treasury", Gate::NeedsFlag("warden_defeated".into(), 1)),
        ),
        Room::new(
            "treasury",
            "Sunken Treasury",
            "Silt-choked coffers, and upon a coral plinth: the Drowned Amulet.",
        )
        .item("amulet")
        .exit("west", Exit::open("warden_hall"))
        .exit("up", Exit::open("sunken_gate")),
        Room::new(
            "sunken_gate",
            "Sunken Gate",
            "A shaft of grey daylight through a broken portcullis — the way out.",
        )
        .exit("down", Exit::open("treasury")),
    ];

    let mut room_map = BTreeMap::new();
    for r in rooms {
        room_map.insert(r.id.clone(), r);
    }

    let use_rules = vec![UseRule {
        room: "vestry".into(),
        item: "rusted_key".into(),
        target: Some("iron_door".into()),
        sets_flag: ("door_unlocked".into(), 1),
        narration: "The rusted key grinds, and the iron door's lock gives with a groan.".into(),
    }];

    let mut hostiles = BTreeMap::new();
    hostiles.insert(
        "warden_hall".to_string(),
        Hostile {
            room: "warden_hall".into(),
            name: "warden".into(),
            defeated_by: "sword".into(),
            victory_flag: ("warden_defeated".into(), 1),
            death_flag: ("slain".into(), 1),
            victory_narration: "Your sword finds the gap in the barnacled plate; the Warden crashes down and moves no more.".into(),
            death_narration: "Bare-handed, you are no match — the Warden's blade takes you, and the vault keeps another bone.".into(),
        },
    );

    GameWorld {
        rooms: room_map,
        use_rules,
        hostiles,
        combat: BTreeMap::new(),
        npcs: Vec::new(),
        dialogue: Vec::new(),
        spells: Vec::new(),
        spell_rules: Vec::new(),
        player_max_hp: 0,
        start: "shore".into(),
        objective: Objective {
            room: "sunken_gate".into(),
            holding: "amulet".into(),
        },
        lose: vec![LoseCondition {
            flag: "slain".into(),
            at_least: 1,
            description: "slain by the Warden".into(),
        }],
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE BRAMBLE KEEP — the second complete adventure, exercising NPCs, bounded
// dialogue, and multi-turn HP combat over a fourteen-room critical path.
// ─────────────────────────────────────────────────────────────────────────────

/// **THE BRAMBLE KEEP** — a complete, solvable fifteen-room adventure in a castle swallowed by a
/// cursed thornwood. Distinct in theme from THE SUNKEN VAULT (a verdant, overgrown ruin, not a
/// drowned one) and built to exercise every new mechanic: an NPC with **world-bounded dialogue**,
/// a **multi-turn HP fight**, light/dark and locked-door gating, and optional side rooms.
///
/// The Sunheart gem sleeps on the Thorn Throne; carry it out to the Broken Rampart to lift the
/// curse and escape. The critical path, in forced order:
///
/// 1. take the **candle** in the gatehouse — the crypt below the courtyard is pitch dark
///    (a [`Gate::NeedsItem`] `candle`);
/// 2. descend to the **crypt** and take the **key** (and, optionally, the **bark_shield** from
///    the orchard, which blunts the Knight's blows);
/// 3. in the courtyard, **use the key on the iron gate** — sets `gate_open`, opening the hall;
/// 4. pick the **nightshade** in the garden;
/// 5. in her hut, **ask the Hedge-Witch about the sickle** — she gives the **silver sickle**
///    ONLY while you hold the nightshade ([`DialogueRule`] `requires` = `NeedsItem("nightshade")`).
///    No flattery moves her: talking is narration; the world grants only what the rule permits;
/// 6. through the hall and up the thorn walk to the approach, **fight the Bramble Knight** — an
///    HP foe felled over several armed strikes with the sickle. Bare-handed it cannot be dented
///    and cuts you down over the turns (a real LOSS: the Knight, not a gate, is what forces the
///    weapon). Felling it sets `knight_felled`, opening the throne;
/// 7. take the **sunheart** on the throne, and carry it up to the **rampart** to WIN.
///
/// Side content off the path: the **well yard**, the **orchard** (the bark_shield), the **chapel**
/// (holy water — lore), the **reliquary** (a thorn-sealed alcove whose living wall is opened by
/// **using the sickle on the thornwall**, `sets thorns_cut` — the [`UseRule`] mechanic, optional),
/// and the **library**, where a **Ghost Scholar** always tells you the keep's history
/// ([`DialogueGrant::Reveals`] — words that reveal a fact but change nothing in the world).
pub fn bramble_keep() -> GameWorld {
    let rooms = vec![
        Room::new(
            "gatehouse",
            "Ruined Gatehouse",
            "A collapsed barbican strangled in ivy; a stub of candle sits in a dead sconce.",
        )
        .item("candle")
        .exit("north", Exit::open("courtyard"))
        .exit("east", Exit::open("well_yard")),
        Room::new(
            "well_yard",
            "Well Yard",
            "A dry well and a coil of rotted rope; brambles have swallowed the far arch.",
        )
        .item("rope")
        .exit("west", Exit::open("gatehouse")),
        Room::new(
            "courtyard",
            "Overgrown Courtyard",
            "A cracked fountain under a canopy of thorns. An iron gate bars the keep's north hall.",
        )
        .exit("south", Exit::open("gatehouse"))
        .exit("east", Exit::open("garden"))
        .exit("west", Exit::open("witch_hut"))
        // The crypt stair is pitch dark — impassable without a light.
        .exit(
            "down",
            Exit::gated("crypt", Gate::NeedsItem("candle".into())),
        )
        // The iron gate opens only once the key has turned it.
        .exit(
            "north",
            Exit::gated("hall", Gate::NeedsFlag("gate_open".into(), 1)),
        ),
        Room::new(
            "garden",
            "Poisoned Garden",
            "Black-petalled nightshade chokes the old herb beds, sweet and deadly.",
        )
        .item("nightshade")
        .exit("west", Exit::open("courtyard"))
        .exit("east", Exit::open("orchard")),
        Room::new(
            "orchard",
            "Withered Orchard",
            "Dead fruit trees; a slab of shaped bark leans against one — a crude shield.",
        )
        .item("bark_shield")
        .exit("west", Exit::open("garden")),
        Room::new(
            "witch_hut",
            "Hedge-Witch's Hut",
            "A leaning hut hung with drying roots; the Hedge-Witch watches from her stool.",
        )
        .exit("east", Exit::open("courtyard")),
        Room::new(
            "crypt",
            "Candlelit Crypt",
            "Stone biers under low arches; a heavy iron key rests on a knight's cold effigy.",
        )
        .item("key")
        .exit("up", Exit::open("courtyard")),
        Room::new(
            "hall",
            "Great Hall",
            "A roofless hall, its banners rotted to threads; passages branch off the dais.",
        )
        .exit("south", Exit::open("courtyard"))
        .exit("west", Exit::open("chapel"))
        .exit("east", Exit::open("library"))
        .exit("north", Exit::open("thorn_walk")),
        Room::new(
            "chapel",
            "Fallen Chapel",
            "A toppled altar; a cracked font still holds a finger of holy water.",
        )
        .item("holy_water")
        .exit("east", Exit::open("hall")),
        Room::new(
            "library",
            "Mouldered Library",
            "Shelves of pulped books; a translucent Ghost Scholar drifts among them, muttering.",
        )
        .exit("west", Exit::open("hall")),
        Room::new(
            "thorn_walk",
            "Thornchoked Walk",
            "A colonnade to the throne approach; a side wall of living thorns seals an alcove west.",
        )
        .exit("south", Exit::open("hall"))
        .exit("north", Exit::open("approach"))
        // The thornwall parts only once it is cut with the sickle — a side alcove, off the path.
        .exit(
            "west",
            Exit::gated("reliquary", Gate::NeedsFlag("thorns_cut".into(), 1)),
        ),
        Room::new(
            "reliquary",
            "Thorn-Sealed Reliquary",
            "A cramped shrine the thorns kept; a tarnished sun-medallion hangs above dead candles.",
        )
        .item("sun_medallion")
        .exit("east", Exit::open("thorn_walk")),
        Room::new(
            "approach",
            "Throne Approach",
            "A short flight to the throne room — and across it, a Bramble Knight grinds awake.",
        )
        .exit("south", Exit::open("thorn_walk"))
        // Sealed until the Bramble Knight is felled.
        .exit(
            "north",
            Exit::gated("throne", Gate::NeedsFlag("knight_felled".into(), 1)),
        ),
        Room::new(
            "throne",
            "The Thorn Throne",
            "Thorns cage a throne of black wood; upon its seat glows the Sunheart.",
        )
        .item("sunheart")
        .exit("south", Exit::open("approach"))
        .exit("up", Exit::open("rampart")),
        Room::new(
            "rampart",
            "Broken Rampart",
            "A shattered wall open to clean sky — beyond the thorns, the road home.",
        )
        .exit("down", Exit::open("throne")),
    ];

    let mut room_map = BTreeMap::new();
    for r in rooms {
        room_map.insert(r.id.clone(), r);
    }

    let use_rules = vec![
        // The iron key turns the gate to the hall.
        UseRule {
            room: "courtyard".into(),
            item: "key".into(),
            target: Some("gate".into()),
            sets_flag: ("gate_open".into(), 1),
            narration: "The iron key bites, and the gate screams open on the north hall.".into(),
        },
        // The silver sickle cuts the living thornwall.
        UseRule {
            room: "thorn_walk".into(),
            item: "sickle".into(),
            target: Some("thornwall".into()),
            sets_flag: ("thorns_cut".into(), 1),
            narration: "The silver sickle shears through the thorns; they wither and fall away."
                .into(),
        },
    ];

    let npcs = vec![
        Npc::new(
            "witch_hut",
            "witch",
            "Hedge-Witch",
            "a green-toothed crone who trades in favours, not flattery",
        ),
        Npc::new(
            "library",
            "scholar",
            "Ghost Scholar",
            "a pale revenant still keeping the keep's records",
        ),
    ];

    let dialogue = vec![
        // WORLD-BOUNDED: the Witch gives the sickle ONLY while you hold the nightshade she wants.
        // No prose can talk it out of her early — talking is narration; the rule decides.
        DialogueRule {
            room: "witch_hut".into(),
            npc: "witch".into(),
            topic: "sickle".into(),
            requires: Some(Gate::NeedsItem("nightshade".into())),
            grant: DialogueGrant::GivesItem("sickle".into()),
            granted_narration: "The Hedge-Witch takes your nightshade, sniffs it, and presses the silver sickle into your palm. 'A fair trade,' she rasps.".into(),
            withheld_narration: "The Hedge-Witch folds her arms. 'Bring me nightshade from the garden, child, and the silver sickle is yours. Not one word sooner.'".into(),
        },
        // A pure-lore grant: the Ghost Scholar always tells you the keep's history, but his words
        // change nothing in the world (Reveals) — the hint has no mechanical power.
        DialogueRule {
            room: "library".into(),
            npc: "scholar".into(),
            topic: "curse".into(),
            requires: None,
            grant: DialogueGrant::Reveals,
            granted_narration: "The Ghost Scholar sighs: 'The Sunheart bound the thornwitch's curse. Cut the thorns, fell her Knight, and carry the gem to open sky — only then does the wood release the keep.'".into(),
            withheld_narration: String::new(),
        },
    ];

    let mut combat = BTreeMap::new();
    combat.insert(
        "approach".to_string(),
        CombatEnemy {
            room: "approach".into(),
            name: "knight".into(),
            hp: 6,
            armed_by: "sickle".into(),
            weapon_damage: 3, // two armed strikes fell it
            unarmed_damage: 0, // bare hands cannot dent thorn-plate
            attack: 3,         // each surviving round it strikes for 3
            armor: Some(("bark_shield".into(), 1)),
            victory_flag: ("knight_felled".into(), 1),
            victory_narration: "The silver sickle hews the Bramble Knight's neck-vine; it comes apart in a rain of dead thorns.".into(),
            hit_narration: "The sickle bites deep — the Knight staggers, then rakes you with a thorned gauntlet.".into(),
            flail_narration: "Your bare blows glance off the thorn-plate; the Knight's gauntlet opens a long red line across you.".into(),
        },
    );

    GameWorld {
        rooms: room_map,
        use_rules,
        hostiles: BTreeMap::new(),
        combat,
        npcs,
        dialogue,
        spells: Vec::new(),
        spell_rules: Vec::new(),
        player_max_hp: 10,
        start: "gatehouse".into(),
        objective: Objective {
            room: "rampart".into(),
            holding: "sunheart".into(),
        },
        lose: vec![LoseCondition {
            flag: PLAYER_WOUNDS_FLAG.into(),
            at_least: 10,
            description: "cut down by the Bramble Knight".into(),
        }],
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE STARFALL SPIRE — the third complete adventure, exercising the bounded MAGIC
// dimension: spells learned from books, cast to cross a dark span, mend a broken
// stair, break a sky-seal, and conjure the one blade a void-thing dreads — a critical
// path that is UNSOLVABLE without casting. The AI narrates the chant; the world
// resolves what the word does.
// ─────────────────────────────────────────────────────────────────────────────

/// **THE STARFALL SPIRE** — a complete, solvable fourteen-room climb up a collapsing wizard's
/// tower, and the showcase for the bounded SPELL system. Distinct in theme from the drowned
/// SUNKEN VAULT and the overgrown BRAMBLE KEEP: a crumbling astronomer's spire whose broken orrery
/// caught a fallen star and began to eat itself. Every rung of the critical path is a SPELL, and
/// the spells are load-bearing — the climb cannot be finished without casting them.
///
/// The magic model, kept honest at every step: a spell is a WORD the world declares
/// ([`Spell`]); you cast it by *speaking it* over the closed [`GameAction::Use`] channel ("cast
/// light"), and the world's [`SpellRule`] — never the AI's prose — decides what it does. A word you
/// have not LEARNED will not come ([`GameRefusal::SpellNotLearned`]); a learned word cast in the
/// wrong place fizzles (a narration turn, no effect); a learned word in the right place does its
/// bounded thing (one cap-gated, on-chain turn). You learn a word by READING its book (a
/// [`UseRule`] that sets `learned_*`). A jailbroken "I cast WISH and become god-king" names no
/// declared spell and touches nothing.
///
/// The critical path, in forced order:
///
/// 1. in the **foyer**, take + **read the Candle Primer** (learn `light`), then **cast light** —
///    silver mage-light opens the dark stair up to the gallery (a [`Gate::NeedsFlag`] `gallery_lit`);
/// 2. in the **gallery**, take the **star chart** and the **Mending Folio**, read the folio (learn
///    `mend`), then **cast mend on the stair** — the shattered span knits (`span_mended`), opening
///    the way up to the landing;
/// 3. on the **landing**, take + read the **Opening Codex** (learn `unlock`); step west to the
///    **observatory** and **ask the Astronomer's Shade for the flame-word** — she gives the
///    **Flare Grimoire** ONLY while you hold the star chart ([`DialogueRule`]); read it (learn `flare`);
/// 4. up in the **orrery hall**, **use the star chart on the orrery** to align it (`orrery_aligned`),
///    THEN **cast unlock on the sky-door** — the seal unwinds (`seal_broken`). Cast unlock before
///    aligning and it FIZZLES (a matching rule whose `requires` is unmet); the world says: not yet;
/// 5. on the **stairhead**, **cast flare** to conjure the **flare blade** (a world-registered,
///    cap-permitted [`SpellEffect::Conjure`]), then **fight the Voidling** — an HP foe felled over
///    three armed strikes. Bare-handed (no flare) it takes no wounds and cuts you down: the spell is
///    the ONLY weapon that works (`voidling_felled` opens the way up);
/// 6. take the **fallen star** in the ruined orrery and carry it up to the **spire crown** under
///    open sky — reach it HOLDING the star to WIN.
///
/// Side content off the path: the **undercroft** and **pantry** (atmosphere + a trinket), the
/// **belltower** whose thorn-locked **reliquary** opens to a SECOND context of `unlock` (a spell
/// used off the critical path), and the **star well** below the observatory (lore).
pub fn starfall_spire() -> GameWorld {
    let rooms = vec![
        Room::new(
            "threshold",
            "Spire Threshold",
            "A cracked marble stair climbs into the ruined tower; a dry cistern gapes below.",
        )
        .exit("up", Exit::open("foyer"))
        .exit("down", Exit::open("undercroft")),
        Room::new(
            "undercroft",
            "Flooded Undercroft",
            "A drowned store-room of broken astrolabes; a knob of tallow floats in the murk.",
        )
        .item("tallow")
        .exit("up", Exit::open("threshold")),
        Room::new(
            "foyer",
            "Candlewax Foyer",
            "A round hall of dead candles. A slim book — the Candle Primer — lies open on a lectern. \
             The stair up is swallowed in unnatural dark.",
        )
        .item("candle_primer")
        .exit("down", Exit::open("threshold"))
        .exit("east", Exit::open("pantry"))
        // The stair up is pitch dark — impassable until the light-word kindles it.
        .exit(
            "up",
            Exit::gated("gallery", Gate::NeedsFlag("gallery_lit".into(), 1)),
        ),
        Room::new(
            "pantry",
            "Ransacked Pantry",
            "Toppled shelves and split sacks; a pinch of moon-salt glitters in the spill.",
        )
        .item("moon_salt")
        .exit("west", Exit::open("foyer")),
        Room::new(
            "gallery",
            "Portrait Gallery",
            "Mage-light picks out rows of sooty portraits. A brass star chart is pinned to one wall, \
             and the Mending Folio rests on a reading-stand. The stair up has collapsed to rubble.",
        )
        .item("star_chart")
        .item("mending_folio")
        .exit("down", Exit::open("foyer"))
        // The shattered stair is impassable until the mend-word knits it.
        .exit(
            "up",
            Exit::gated("landing", Gate::NeedsFlag("span_mended".into(), 1)),
        ),
        Room::new(
            "landing",
            "Cracked Landing",
            "A wide landing under a leaning arch; the Opening Codex is chained to a reading-desk. \
             Doors lead off to an observatory and a belltower; the orrery hall waits above.",
        )
        .item("opening_codex")
        .exit("down", Exit::open("gallery"))
        .exit("west", Exit::open("observatory"))
        .exit("east", Exit::open("belltower"))
        .exit("up", Exit::open("orrery_hall")),
        Room::new(
            "observatory",
            "Ruined Observatory",
            "A shattered dome open to the night. The Astronomer's Shade drifts by a cracked telescope, \
             still charting stars that fell long ago.",
        )
        .exit("east", Exit::open("landing"))
        .exit("down", Exit::open("star_well")),
        Room::new(
            "star_well",
            "The Star Well",
            "A deep shaft the old mages dropped plumb-lines down; a tarnished astrolabe hangs on a nail.",
        )
        .item("astrolabe")
        .exit("up", Exit::open("observatory")),
        Room::new(
            "belltower",
            "Silent Belltower",
            "A cracked bell hangs still. A small alcove in the west wall is sealed by an old ward-lock.",
        )
        .exit("west", Exit::open("landing"))
        // A side alcove sealed by a ward — opened by a SECOND context of the unlock-word (optional).
        .exit(
            "north",
            Exit::gated("reliquary", Gate::NeedsFlag("reliquary_open".into(), 1)),
        ),
        Room::new(
            "reliquary",
            "Warded Reliquary",
            "A cramped vault the ward kept shut for an age; a silver orrery-charm rests on velvet.",
        )
        .item("silver_orrery")
        .exit("south", Exit::open("belltower")),
        Room::new(
            "orrery_hall",
            "The Orrery Hall",
            "A great brass orrery fills the room, its rings frozen mid-turn. Above it, a sky-door is \
             bound shut by a shimmering seal.",
        )
        .exit("down", Exit::open("landing"))
        // The sky-door's seal is broken only by the unlock-word — and only once the orrery is aligned.
        .exit(
            "up",
            Exit::gated("stairhead", Gate::NeedsFlag("seal_broken".into(), 1)),
        ),
        Room::new(
            "stairhead",
            "Windswept Stairhead",
            "A narrow stair open to the void beyond the seal — and across it coils a Voidling, a knot \
             of starless dark that hates the light.",
        )
        .exit("down", Exit::open("orrery_hall"))
        // Sealed until the Voidling is felled.
        .exit(
            "up",
            Exit::gated("orrery", Gate::NeedsFlag("voidling_felled".into(), 1)),
        ),
        Room::new(
            "orrery",
            "The Broken Orrery",
            "The tower's crown-works, wrenched apart around a socket where a fallen star still burns.",
        )
        .item("fallen_star")
        .exit("down", Exit::open("stairhead"))
        .exit("up", Exit::open("crown")),
        Room::new(
            "crown",
            "The Spire Crown",
            "The open summit under a wheeling sky — the star's empty cradle waits to be filled.",
        )
        .exit("down", Exit::open("orrery")),
    ];

    let mut room_map = BTreeMap::new();
    for r in rooms {
        room_map.insert(r.id.clone(), r);
    }

    // READING a spellbook is a bare `Use` of the book that sets its `learned_*` flag — this is how a
    // spell is LEARNED (the Spell's `learned` gate reads the flag). And the orrery is aligned by
    // using the star chart on it — the precondition the sky-door's unlock requires.
    let use_rules = vec![
        UseRule {
            room: "foyer".into(),
            item: "candle_primer".into(),
            target: None,
            sets_flag: ("learned_light".into(), 1),
            narration: "You pore over the Candle Primer; the light-word settles onto your tongue.".into(),
        },
        UseRule {
            room: "gallery".into(),
            item: "mending_folio".into(),
            target: None,
            sets_flag: ("learned_mend".into(), 1),
            narration: "The Mending Folio's diagrams resolve into sense; the mend-word is yours.".into(),
        },
        UseRule {
            room: "landing".into(),
            item: "opening_codex".into(),
            target: None,
            sets_flag: ("learned_unlock".into(), 1),
            narration: "The Opening Codex yields its cipher; the unlock-word takes root in memory.".into(),
        },
        UseRule {
            room: "observatory".into(),
            item: "flare_grimoire".into(),
            target: None,
            sets_flag: ("learned_flare".into(), 1),
            narration: "The Flare Grimoire's char-black pages breathe heat; the flame-word catches in you.".into(),
        },
        UseRule {
            room: "orrery_hall".into(),
            item: "star_chart".into(),
            target: Some("orrery".into()),
            sets_flag: ("orrery_aligned".into(), 1),
            narration: "You turn the brass rings to match the star chart; the orrery locks into alignment with a deep chime.".into(),
        },
    ];

    let npcs = vec![Npc::new(
        "observatory",
        "astronomer",
        "Astronomer's Shade",
        "a translucent star-keeper who trades in charts, not flattery",
    )];

    let dialogue = vec![
        // WORLD-BOUNDED: the Shade gives the Flare Grimoire ONLY while you hold the star chart.
        // No prose talks the flame-word out of her early — the DialogueRule decides.
        DialogueRule {
            room: "observatory".into(),
            npc: "astronomer".into(),
            topic: "flame".into(),
            requires: Some(Gate::NeedsItem("star_chart".into())),
            grant: DialogueGrant::GivesItem("flare_grimoire".into()),
            granted_narration: "The Shade studies your star chart, nods once, and lifts a charred grimoire from the ash: 'The flame-word. You will need it above.'".into(),
            withheld_narration: "The Shade turns away. 'Bring me the star chart from the gallery, and the flame-word is yours. Not one breath sooner.'".into(),
        },
        // Pure lore — the Shade tells you the spire's plight, but her words change nothing.
        DialogueRule {
            room: "observatory".into(),
            npc: "astronomer".into(),
            topic: "stars".into(),
            requires: None,
            grant: DialogueGrant::Reveals,
            granted_narration: "'A star fell into the orrery, and the tower began to eat itself. Light your way up, mend what broke, break the sky-seal, and set the star back in its cradle — only then does the spire fall still.'".into(),
            withheld_narration: String::new(),
        },
    ];

    let spells = vec![
        Spell {
            word: "light".into(),
            learned: Some(Gate::NeedsFlag("learned_light".into(), 1)),
        },
        Spell {
            word: "mend".into(),
            learned: Some(Gate::NeedsFlag("learned_mend".into(), 1)),
        },
        Spell {
            word: "unlock".into(),
            learned: Some(Gate::NeedsFlag("learned_unlock".into(), 1)),
        },
        Spell {
            word: "flare".into(),
            learned: Some(Gate::NeedsFlag("learned_flare".into(), 1)),
        },
    ];

    let spell_rules = vec![
        // light — cast in the foyer, kindles the dark stair up to the gallery.
        SpellRule {
            room: "foyer".into(),
            spell: "light".into(),
            target: None,
            requires: None,
            effect: SpellEffect::SetFlag("gallery_lit".into(), 1),
            narration: "Silver mage-light blooms from your palm and pours up the stair; the gallery above brightens.".into(),
            fizzle_narration: String::new(),
        },
        // mend — cast on the shattered stair in the gallery, knitting the span.
        SpellRule {
            room: "gallery".into(),
            spell: "mend".into(),
            target: Some("stair".into()),
            requires: None,
            effect: SpellEffect::SetFlag("span_mended".into(), 1),
            narration: "The mend-word knits the shattered stair; stone flows back into stone and the span holds.".into(),
            fizzle_narration: String::new(),
        },
        // unlock — breaks the sky-door's seal, but ONLY once the orrery is aligned (requires);
        // cast before aligning, it fizzles.
        SpellRule {
            room: "orrery_hall".into(),
            spell: "unlock".into(),
            target: Some("sky_door".into()),
            requires: Some(Gate::NeedsFlag("orrery_aligned".into(), 1)),
            effect: SpellEffect::SetFlag("seal_broken".into(), 1),
            narration: "The sky-door's seal unwinds at the word, thread by thread, and the way above opens.".into(),
            fizzle_narration: "The unlock-word scrapes uselessly at the sky-seal — the orrery is not yet aligned to loose it.".into(),
        },
        // unlock — a SECOND context (off the critical path): opens the belltower's warded alcove.
        SpellRule {
            room: "belltower".into(),
            spell: "unlock".into(),
            target: Some("alcove".into()),
            requires: None,
            effect: SpellEffect::SetFlag("reliquary_open".into(), 1),
            narration: "The unlock-word coaxes the alcove's old ward; it clicks, and the reliquary yawns open.".into(),
            fizzle_narration: String::new(),
        },
        // flare — conjures the flare blade, the one weapon the Voidling dreads (cap-permitted).
        SpellRule {
            room: "stairhead".into(),
            spell: "flare".into(),
            target: None,
            requires: None,
            effect: SpellEffect::Conjure("flare_blade".into()),
            narration: "You speak the flame-word and a blade of white fire kindles in your grip — the one thing a void-thing dreads.".into(),
            fizzle_narration: String::new(),
        },
    ];

    let mut combat = BTreeMap::new();
    combat.insert(
        "stairhead".to_string(),
        CombatEnemy {
            room: "stairhead".into(),
            name: "voidling".into(),
            hp: 9,
            armed_by: "flare_blade".into(),
            weapon_damage: 3,  // three flame-strikes fell it
            unarmed_damage: 0, // bare hands (no flare) never wound the dark
            attack: 3,         // each surviving round it rakes you for 3
            armor: None,
            victory_flag: ("voidling_felled".into(), 1),
            victory_narration: "The flare blade sears through the knot of dark; the Voidling unravels into cold sparks and is gone.".into(),
            hit_narration: "White fire bites the Voidling — it recoils, then lashes back with a tendril of starless cold.".into(),
            flail_narration: "Your bare strike passes through the Voidling like smoke; its cold tendril opens a numbing wound across you.".into(),
        },
    );

    GameWorld {
        rooms: room_map,
        use_rules,
        hostiles: BTreeMap::new(),
        combat,
        npcs,
        dialogue,
        spells,
        spell_rules,
        player_max_hp: 10,
        start: "threshold".into(),
        objective: Objective {
            room: "crown".into(),
            holding: "fallen_star".into(),
        },
        lose: vec![LoseCondition {
            flag: PLAYER_WOUNDS_FLAG.into(),
            at_least: 10,
            description: "cut down by the Voidling".into(),
        }],
    }
}

#[cfg(test)]
mod tests;
