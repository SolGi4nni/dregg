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
//! * **[`crate::DmCaps`]** is a fail-closed grant whitelist: a `GrantItem` for an item not on
//!   it is refused, so nothing can mint an item the world never named. Honest precision: inside a
//!   [`GameSession`] the whitelist is *derived* from the world's own item set
//!   ([`GameWorld::all_items`] = room items ∪ dialogue grants ∪ conjures), so every grant the
//!   resolver can emit is always on it — the cap cannot fire *independently* here; the true bound
//!   on grants is the resolver. The cap becomes independently load-bearing on the lower-level
//!   [`DungeonMaster::narrate_move`] API, where a caller supplies the item and an off-list one is
//!   refused. Within a session it is a correct backstop, not a second independent tooth.

use std::collections::{BTreeMap, BTreeSet};

use dregg_dice::{
    CommitReveal, Deterministic, DrawStream, EvidenceKind, Hybrid, MockBeacon, RandomnessEvidence,
    RandomnessRequest, RandomnessSource, Seed, ServerVrf, VerifyError,
};

use crate::{
    slot_confined, world_binding, DmError, DmMove, DungeonMaster, LoadError, PromptBinding,
    RandomnessRecord, Receipt, RecordedDm, WorldCell, WorldEffect,
};

/// Domain separator for [`GameWorld::game_binding`] — the committed game identity a randomness
/// draw binds. Distinct from every other hashed object so a game binding can never collide with
/// a state root, an event id, or a receipt id.
const GAME_BINDING_DOMAIN: &[u8] = b"attested-dm-game-binding-v1";

/// Domain separator for [`action_commitment`] — the finalized typed-action hash a randomness
/// draw binds into its event id, so a re-aimed action moves the seed and is caught on replay.
const ACTION_COMMITMENT_DOMAIN: &[u8] = b"attested-dm-action-commitment-v1";

/// The purpose tag ([`dregg_dice::EventId`] `event_kind`) for a loot-chest draw — domain-separating
/// this subsystem's draws from any other (a combat roll, say) so they can never influence one another.
pub const LOOT_EVENT_KIND: &str = "loot";

// ─────────────────────────────────────────────────────────────────────────────
// The closed typed action channel — the ONLY moves the AI can propose.
// ─────────────────────────────────────────────────────────────────────────────

/// **The closed, typed action a dungeon-master may propose.** This is the whole channel
/// through which the AI can attempt to change the world — it cannot emit free-text state
/// mutations, only *name* one of these moves. The [`resolve_action`] resolver then decides
/// what (if anything) actually happens. Riding the chain via [`GameBinding`], the on-ledger
/// receipt commits to exactly which typed move produced each turn.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
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
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
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

// ─────────────────────────────────────────────────────────────────────────────
// LIGHT — a bounded RESOURCE dimension. A lit lamp burns down one turn per STEP; the
// dark rooms are impassable without it; refuel with oil, or the dark takes you. The AI
// narrates the flame however it likes ("your lamp blazes eternal"); the WORLD keeps the
// oil counter, and the counter is the truth. Prose is not power, at the level of light.
// ─────────────────────────────────────────────────────────────────────────────

/// **A world-declared LIGHT budget — the resource dimension.** A lit lamp burns down one
/// turn per STEP: every legal [`GameAction::Move`] taken while the player HOLDS the
/// [`Self::lamp`] decrements the [`Self::counter`] flag by one — a [`WorldEffect::SetFlag`]
/// batched onto the same on-chain move (the resolver reads the counter and writes `counter - 1`;
/// the count is a world flag, never the AI's prose). A room in [`Self::dark_rooms`] is
/// IMPASSABLE without a burning lamp: entering it requires the player to hold the lamp AND
/// `counter > 0`, else the move is REFUSED ([`GameRefusal::TooDark`]) — the dark is absolute,
/// and a jailbroken *"your lamp blazes eternal"* lights nothing; only real oil in the counter does.
///
/// The lamp is refueled by an ordinary [`RefuelRule`] (use oil on the lamp → `+add` turns), each
/// oil flask single-use (it sets a `spent_*` flag, so a second pour of the empty flask does
/// nothing). Run the counter to zero while stepping INTO the dark and the dark takes you: the step
/// whose last oil is spent entering a dark room strands the player ([`Self::stranded`] flag → a
/// [`LoseCondition`]). Light never grants an item and never opens a non-light [`Gate`]; it composes
/// with the caps and the gates, it does not bypass them.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct LightRule {
    /// The world flag holding the remaining lamp-turns (the light budget). Seeded to
    /// [`Self::start`] when the world opens ([`GameWorld::new_world`]); decremented on-chain per step.
    pub counter: String,
    /// The lamp item. The light burns only while it is HELD (a step without it costs no oil), and a
    /// dark room is impassable without it — no lamp, no descent.
    pub lamp: String,
    /// The lamp's initial oil — the counter's value when the world opens.
    pub start: i64,
    /// The pitch-dark rooms — impassable unless the player holds the lamp AND `counter > 0`.
    pub dark_rooms: BTreeSet<String>,
    /// The single-use refuel interactions (use oil on the lamp → more turns).
    pub refuels: Vec<RefuelRule>,
    /// The flag set when the lamp gutters out in the dark (the last oil spent STEPPING INTO a dark
    /// room) — a stranded LOSE. Wire it as a [`LoseCondition`]. `None` = no stranded lose.
    pub stranded: Option<(String, i64)>,
}

impl LightRule {
    /// Whether `room` is pitch dark (needs a burning lamp to enter).
    pub fn is_dark(&self, room: &str) -> bool {
        self.dark_rooms.contains(room)
    }

    /// The remaining lamp-oil in the current world.
    pub fn oil(&self, world: &WorldCell) -> i64 {
        world.flags.get(&self.counter).copied().unwrap_or(0)
    }

    /// Whether the lamp is BURNING right now — held, with oil left. Only a burning lamp lets a
    /// player enter the dark, and only a burning lamp burns oil on a step.
    pub fn burning(&self, world: &WorldCell) -> bool {
        world.inventory.contains(&self.lamp) && self.oil(world) > 0
    }

    /// The refuel rule for pouring `fuel_item` into the lamp, if the world declares one.
    pub fn refuel_for(&self, fuel_item: &str) -> Option<&RefuelRule> {
        self.refuels.iter().find(|r| r.fuel_item == fuel_item)
    }
}

/// **A single-use REFUEL interaction** — pour oil into the lamp to buy more turns. When the player
/// uses [`Self::fuel_item`] on the lamp (a [`GameAction::Use`] whose target is the lamp, or a bare
/// pour) and this flask is not yet spent, the light counter GAINS [`Self::add`] turns (the resolver
/// reads the current counter and writes `counter + add`) AND [`Self::spent_flag`] is set — the flask
/// empties, so a second pour does nothing. Both flag writes land as ONE [`WorldEffect::Batch`] turn,
/// bound on-chain. The oil is single-use because the world tracks the spent flag, not the prose: a
/// jailbroken *"the flask refills itself endlessly"* pours nothing once the flag is set.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RefuelRule {
    /// The oil the player must HOLD to refuel (e.g. `oil_flask_b`).
    pub fuel_item: String,
    /// The turns added to the light counter on a successful pour.
    pub add: i64,
    /// The per-flask guard flag: once set, this flask is spent (a second pour does nothing).
    pub spent_flag: String,
    /// The world's account of a successful refuel.
    pub narration: String,
    /// The world's account of pouring an already-spent flask (no effect).
    pub spent_narration: String,
}

// ─────────────────────────────────────────────────────────────────────────────
// CONSUMABLES + STATUS EFFECTS — a bounded ITEM-USE + TIMED-EFFECT dimension. A
// consumable is `use`d (riding the closed `Use` channel, exactly as a spell or an NPC
// trade does — NO new GameAction), applies a WORLD-BOUNDED effect, and is CONSUMED
// (removed from inventory, so a second use finds nothing). A status is a timed world
// flag: a `shield` buff that mitigates combat while it lasts, or a `poison` debuff that
// ticks a wound each STEP — decremented one per step the way light-oil burns. The AI
// narrates the draught however it likes ("this elixir makes you INVINCIBLE"); the world
// heals exactly the rule's N and not one point more. Prose is not power, at the level of
// what you drink.
// ─────────────────────────────────────────────────────────────────────────────

/// **What a status FLAG does while it is active** (its counter `> 0`). A status is a plain world
/// flag holding its remaining turns; every step decrements it by one (see [`GameWorld::statuses`]
/// and the move bookkeeping), and while it is above zero the world reads its [`StatusKind`] into
/// the mechanics — combat mitigation for a [`Self::Shield`], a per-step wound for a
/// [`Self::Poison`]. The AI never writes a status value; only a world-bounded effect (a consumable,
/// the step-decrement, a cure) does.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StatusKind {
    /// A BUFF: while active, mitigates `mitigate` damage off every blow a [`CombatEnemy`] lands
    /// (stacking with worn [`CombatEnemy::armor`]) — a shield-elixir you drink before a boss.
    Shield(i64),
    /// A DEBUFF: while active, adds `damage` to [`PLAYER_WOUNDS_FLAG`] on every STEP taken (the
    /// same on-chain move that decrements the counter) — a venom that races you to a cure.
    Poison(i64),
}

/// **A timed status the world declares** — a buff/debuff carried as a world flag [`Self::flag`]
/// holding its remaining turns. It is set to a duration by a consumable ([`ConsumableEffect::Status`]),
/// decremented one per step (like light-oil), and cleared by a cure ([`ConsumableEffect::Cure`]) — all
/// world-bounded flag writes; the count is the truth, never the prose. What it DOES while active is its
/// [`Self::kind`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StatusRule {
    /// The world flag holding this status's remaining turns (`> 0` = active).
    pub flag: String,
    /// What the status does while active — a [`StatusKind::Shield`] buff or [`StatusKind::Poison`] debuff.
    pub kind: StatusKind,
}

impl StatusRule {
    /// The status's remaining turns in the current world (`0` if never applied).
    pub fn remaining(&self, world: &WorldCell) -> i64 {
        world.flags.get(&self.flag).copied().unwrap_or(0)
    }

    /// Whether the status is active right now (its counter `> 0`).
    pub fn active(&self, world: &WorldCell) -> bool {
        self.remaining(world) > 0
    }
}

/// **The bounded effect a consumable has when it is `use`d.** This is the whole affordance of a
/// consumable: it can HEAL (reduce [`PLAYER_WOUNDS_FLAG`] by a fixed N, clamped at zero — a
/// jailbroken over-heal narration cannot exceed N), grant a timed [`StatusRule`] (set its flag to a
/// duration), CURE a status (zero its flag), set a plain world flag a downstream [`Gate`] reads, or
/// REVEAL (pure lore, no world change beyond the consumption). Every case is a plain, cap-gated
/// [`WorldEffect`] batched with the [`WorldEffect::ConsumeItem`] that removes the item — a consumable
/// can never grant an off-whitelist item or open a non-declared gate; it composes with the caps and
/// the gates, it does not bypass them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConsumableEffect {
    /// Reduce [`PLAYER_WOUNDS_FLAG`] by `n`, clamped at zero (a healing draught). The world heals
    /// EXACTLY `n`; no narration heals more.
    Heal(i64),
    /// Grant a timed status: set the named status flag to `duration` turns (a buff/debuff draught).
    /// The flag must be a declared [`StatusRule`].
    Status {
        /// The status flag to set (a declared [`StatusRule::flag`]).
        flag: String,
        /// The number of turns to grant.
        duration: i64,
    },
    /// Cure a status: set the named status flag to zero (an antidote). The flag should be a declared
    /// [`StatusRule`].
    Cure(String),
    /// Set a plain world flag (name, value) — a consumable whose bounded effect is a flag a
    /// downstream [`Gate`] reads.
    SetFlag(String, i64),
    /// No world change beyond the consumption — a consumable that only reveals lore as it is used.
    Reveal,
}

/// **A consumable the world declares** — an item that, when `use`d (riding [`GameAction::Use`]), does
/// a bounded [`ConsumableEffect`] and is CONSUMED (a [`WorldEffect::ConsumeItem`] removes it from the
/// inventory, so it cannot be used twice). Using a consumable you do not hold is refused
/// ([`GameRefusal::NotHolding`]) — and once spent, the item is gone, so a second use is refused the
/// same way (world unchanged, no receipt: the anti-ghost tooth). A consumable is usable wherever you
/// hold it (it is not room-scoped), matching how a potion travels in your pack.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConsumableRule {
    /// The item that is consumed. It must be a world-registered ([`GameWorld::all_items`]) item.
    pub item: String,
    /// The bounded effect the consumable has when used.
    pub effect: ConsumableEffect,
    /// The world's account of using it (distinct from the AI's flavour narration).
    pub narration: String,
}

// ─────────────────────────────────────────────────────────────────────────────
// LOOT — a bounded, PROVABLY-FAIR randomness dimension. A loot chest, on `Use`, drops ONE item
// from a committed loot table via a single unbiased d-N draw. The outcome is WORLD-RESOLVED from
// a verified `dregg_dice` draw stream — never the AI's prose — and BOUNDED to the declared table.
// The draw's `RandomnessRequest` (event id over game/seq/pre-state/action/purpose/draw-count) +
// its `RandomnessEvidence` ride the receipt chain, and `verify_replay` reconstructs + re-verifies
// the whole draw. Prose is not power, at the level of chance: a jailbroken "the chest brims with
// crowns" drops exactly `table[draw]` and not one thing more.
// ─────────────────────────────────────────────────────────────────────────────

/// **A world-declared LOOT CHEST — the provably-fair randomness mechanic.** The chest is a room
/// fixture addressed by name (a bare [`GameAction::Use`] of [`Self::chest`], like casting a spell or
/// hailing an NPC — you do not hold it). On its first `Use` in [`Self::room`] the world takes ONE
/// unbiased draw over `0..table.len()` from the turn's verified [`dregg_dice::DrawStream`] and grants
/// exactly [`Self::table`]`[draw]` — a [`WorldEffect::Batch`] of the [`WorldEffect::GrantItem`] and the
/// [`Self::opened_flag`] set to 1, landed as ONE receipted turn carrying the draw's
/// [`crate::RandomnessRecord`]. The drop VARIES BY SEED but is fully reconstructible: a verifier
/// re-derives the event id, re-verifies the evidence to recover the seed, rebuilds the stream, and
/// re-runs this same resolution. A second `Use` of an already-opened chest is a legal no-op
/// ([`Self::empty_narration`]) that draws nothing — so the randomness is consumed exactly once.
///
/// Every table entry MUST be a world-registered item ([`GameWorld::all_items`] unions the table), so
/// the grant is cap-permitted: a chest can never drop an item the world never named.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LootRule {
    /// The room the chest stands in.
    pub room: String,
    /// The chest's name — the `Use` target that opens it (e.g. `Use("reliquary_chest", None)`).
    pub chest: String,
    /// The committed loot table — the closed set of possible drops. The draw picks one index
    /// `0..table.len()` unbiasedly. Must be non-empty (the DSL/authoring validates this).
    pub table: Vec<String>,
    /// The world flag set to 1 once the chest is opened — makes the draw single-use (a second
    /// `Use` finds it open and draws nothing).
    pub opened_flag: String,
    /// The world's account when the chest opens (the drawn item is appended by the resolver).
    pub narration: String,
    /// The world's account of `Use`-ing an already-opened chest (a legal no-op, no draw).
    pub empty_narration: String,
}

impl LootRule {
    /// A loot chest builder over a committed table.
    pub fn new(
        room: impl Into<String>,
        chest: impl Into<String>,
        table: impl IntoIterator<Item = impl Into<String>>,
    ) -> LootRule {
        let chest = chest.into();
        let opened_flag = format!("opened_{chest}");
        LootRule {
            room: room.into(),
            chest,
            table: table.into_iter().map(Into::into).collect(),
            opened_flag,
            narration: "The chest grinds open".into(),
            empty_narration: "The chest lies open and empty — nothing more to draw.".into(),
        }
    }

    /// Whether this chest has already been opened in `world` (its draw already consumed).
    pub fn opened(&self, world: &WorldCell) -> bool {
        world.flags.get(&self.opened_flag).copied().unwrap_or(0) >= 1
    }
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
    /// The consumables this world declares — items that, when `use`d, apply a bounded effect and are
    /// consumed. Empty for a dungeon with no consumable dimension (the original four), so the
    /// mechanic is purely additive. See [`ConsumableRule`].
    pub consumables: Vec<ConsumableRule>,
    /// The timed statuses this world declares — buffs/debuffs carried as flags, decremented per step.
    /// Empty for a dungeon with no status dimension (the original four). See [`StatusRule`].
    pub statuses: Vec<StatusRule>,
    /// The provably-fair LOOT CHESTS this world declares — fixtures that, on `Use`, drop a
    /// seed-determined item from a committed table via a verifiable draw. Empty for a dungeon with
    /// no randomness dimension (the five bundled games), so the mechanic is purely additive. See
    /// [`LootRule`].
    pub loot: Vec<LootRule>,
    /// The player's maximum hit points — accumulated [`PLAYER_WOUNDS_FLAG`] `>=` this is death
    /// (wire it as a [`LoseCondition`] for a combat dungeon). Non-combat dungeons ignore it.
    pub player_max_hp: i64,
    /// The optional LIGHT budget — a lit lamp that burns down per step, dark rooms impassable
    /// without it, and single-use oil to refuel. `None` for a dungeon with no light dimension (the
    /// original three), so the resource mechanic is purely additive. See [`LightRule`].
    pub light: Option<LightRule>,
    /// The starting room id.
    pub start: String,
    /// The win objective.
    pub objective: Objective,
    /// The lose conditions.
    pub lose: Vec<LoseCondition>,
}

impl GameWorld {
    /// A fresh [`WorldCell`] opened at this world's starting room. If the world declares a
    /// [`LightRule`], the lamp's initial oil is seeded into its counter flag (genesis world
    /// config, like the starting room) — every later change to the counter is an on-chain turn.
    pub fn new_world(&self) -> WorldCell {
        let mut world = WorldCell::new(self.start.clone());
        if let Some(light) = &self.light {
            world.flags.insert(light.counter.clone(), light.start);
        }
        world
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
        // Every loot-table entry a chest can drop is world-registered, so the drop is a
        // cap-permitted grant — a chest can never mint an item the world never named.
        for rule in &self.loot {
            for item in &rule.table {
                items.insert(item.clone());
            }
        }
        items
    }

    /// The loot chest named `chest` standing in `room`, if the world declares one. A bare `Use` of
    /// a chest name in its room routes to [`resolve_loot`]; anything else falls through.
    pub fn loot_rule(&self, room: &str, chest: &str) -> Option<&LootRule> {
        self.loot
            .iter()
            .find(|r| r.room == room && r.chest == chest)
    }

    /// **The committed game identity** a randomness draw binds (the `game_binding` of a
    /// [`RandomnessRequest`]). A domain-separated hash over the ruleset that matters for a draw —
    /// the objective and the loot tables — so a draw's event id is bound to THIS world's rules; a
    /// verifier recomputes it from the same static map. (Production would fold a VRF key epoch +
    /// full ruleset hash here; this binds the loot-relevant surface.)
    pub fn game_binding(&self) -> Vec<u8> {
        let mut h = blake3::Hasher::new();
        h.update(GAME_BINDING_DOMAIN);
        h.update(self.objective.room.as_bytes());
        h.update(&[0u8]);
        h.update(self.objective.holding.as_bytes());
        h.update(&[0u8]);
        h.update(&(self.loot.len() as u64).to_le_bytes());
        for rule in &self.loot {
            h.update(&(rule.room.len() as u64).to_le_bytes());
            h.update(rule.room.as_bytes());
            h.update(&(rule.chest.len() as u64).to_le_bytes());
            h.update(rule.chest.as_bytes());
            h.update(&(rule.table.len() as u64).to_le_bytes());
            for item in &rule.table {
                h.update(&(item.len() as u64).to_le_bytes());
                h.update(item.as_bytes());
            }
        }
        h.finalize().as_bytes().to_vec()
    }

    /// Whether `word` is a spell this world declares (its casting vocabulary). A word that is NOT
    /// declared is an unknown incantation — the resolver never routes it to magic.
    pub fn is_spell_word(&self, word: &str) -> bool {
        self.spells.iter().any(|s| s.word == word)
    }

    /// The consumable rule for `item`, if the world declares one. A `use` of a declared consumable
    /// (that the player holds) routes to [`resolve_consumable`]; a non-consumable falls through.
    pub fn consumable(&self, item: &str) -> Option<&ConsumableRule> {
        self.consumables.iter().find(|c| c.item == item)
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
    /// The destination room is pitch dark and cannot be entered: the player holds no burning lamp,
    /// or the lamp's oil is spent (`counter == 0`). The dark is ABSOLUTE — no prose ("your lamp
    /// blazes eternal") lights it; only real oil in the counter does. World unchanged, no receipt
    /// (anti-ghost). See [`LightRule`].
    TooDark {
        /// The dark room the player could not enter.
        room: String,
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
            GameRefusal::TooDark { room } => {
                write!(
                    f,
                    "the way into the {room} is pitch dark — without a burning lamp you cannot \
                     enter (your light is spent)"
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
    resolve_action_rng(map, world, action, None)
}

/// **THE RESOLVER, with verifiable randomness threaded in.** The deterministic core of
/// [`resolve_action`] plus one optional argument: `rng`, the turn's verified
/// [`dregg_dice::DrawStream`] (rebuilt from a checked seed). Every deterministic action ignores it;
/// the loot-chest mechanic consumes it to produce a WORLD-RESOLVED, seed-determined drop. The live
/// session and the replay verifier both call this with the SAME reconstructed stream, so a random
/// turn resolves identically when played and when re-executed — the property replay checks.
///
/// `rng` is `None` on the plain [`resolve_action`] path (deterministic callers). A random action
/// reaching that path draws nothing (a fail-closed no-op); the live and replay flows always seed a
/// loot turn, so that case never arises in a valid history.
pub fn resolve_action_rng(
    map: &GameWorld,
    world: &WorldCell,
    action: &GameAction,
    rng: Option<&DrawStream>,
) -> Outcome {
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
            let dest_name = map
                .rooms
                .get(&exit.to_room)
                .map(|r| r.name.clone())
                .unwrap_or_else(|| exit.to_room.clone());
            // LIGHT: a pitch-dark room is impassable without a BURNING lamp (held AND oil > 0). The
            // dark is absolute — the resolver refuses the step no matter how the AI narrates the
            // flame. World unchanged, no receipt (anti-ghost). Composed with, not replacing, gates.
            if let Some(light) = &map.light {
                if light.is_dark(&exit.to_room) && !light.burning(world) {
                    return Outcome::Refused(GameRefusal::TooDark {
                        room: dest_name.clone(),
                    });
                }
            }
            // The move advances the scene, and — if a lit lamp is carried — BURNS one oil this step
            // (a SetFlag batched onto the same on-chain move; the world writes the counter, not the
            // prose). If that last oil is spent STEPPING INTO the dark, the lamp gutters out and the
            // dark takes the player (the stranded flag → a LoseCondition). All in one receipted turn.
            let effect = Some(move_effect(map, world, &exit.to_room));
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
            // LOOT PATH: a world-declared loot chest addressed by name in this room (a bare `Use`).
            // The chest is a fixture, not a held item, so this branches BEFORE the holding check —
            // exactly like the spell / NPC paths. Opening it draws ONE item from the committed table
            // via the turn's verified `rng` stream; the WORLD picks the drop, never the AI's prose.
            if target.is_none() {
                if let Some(loot) = map.loot_rule(&here, item) {
                    return resolve_loot(map, world, loot, rng);
                }
            }
            if !world.inventory.contains(item) {
                return Outcome::Refused(GameRefusal::NotHolding(item.clone()));
            }
            // REFUEL PATH: pouring a held oil flask into the lamp (a bare pour, or `use oil on lamp`).
            // The world's RefuelRule — not the prose — decides: an unspent flask adds its oil to the
            // counter and marks itself spent (one Batch turn); an already-spent flask pours nothing.
            if let Some(light) = &map.light {
                let aimed_at_lamp = target.is_none() || target.as_deref() == Some(&light.lamp);
                if aimed_at_lamp {
                    if let Some(refuel) = light.refuel_for(item) {
                        return resolve_refuel(map, world, light, refuel);
                    }
                }
            }
            // CONSUMABLE PATH: a held, world-declared consumable applies its bounded effect and is
            // consumed (removed from inventory) — one Batch turn. Reached only past the holding check
            // above, so a spent consumable (already gone from inventory) never gets here: it refused
            // with NotHolding, no receipt. The prose has no power over what the draught does.
            if let Some(consumable) = map.consumable(item) {
                return resolve_consumable(map, world, consumable);
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

/// **Resolve a refuel** — pour a held oil flask into the lamp. The world decides, not the prose:
/// an UNSPENT flask adds its oil to the light counter and marks itself spent (both writes in one
/// [`WorldEffect::Batch`], so a rewritten refuel breaks the receipt); an ALREADY-SPENT flask is
/// empty and pours nothing (a legal narration turn, no effect — the flask does not refill itself
/// however the AI narrates it). The oil counter is a world flag; the count is the truth.
fn resolve_refuel(
    _map: &GameWorld,
    world: &WorldCell,
    light: &LightRule,
    refuel: &RefuelRule,
) -> Outcome {
    // An already-spent flask is dry — a legal turn that changes nothing (like a fizzled spell).
    if world.flags.get(&refuel.spent_flag).copied().unwrap_or(0) >= 1 {
        return Outcome::Legal(Resolution {
            narration: refuel.spent_narration.clone(),
            status: status_after(_map, world, None),
            effect: None,
        });
    }
    let topped = light.oil(world) + refuel.add;
    let effect = Some(WorldEffect::Batch(vec![
        WorldEffect::SetFlag(light.counter.clone(), topped),
        WorldEffect::SetFlag(refuel.spent_flag.clone(), 1),
    ]));
    Outcome::Legal(Resolution {
        narration: refuel.narration.clone(),
        status: status_after(_map, world, effect.as_ref()),
        effect,
    })
}

/// **Resolve a consumable** — drink the potion; the world decides what it does, not the prose. The
/// bounded [`ConsumableEffect`] is applied AND the item is removed ([`WorldEffect::ConsumeItem`]) in
/// ONE [`WorldEffect::Batch`] (so a rewritten consume breaks the receipt), leaving the world in a
/// single verified turn. A HEAL reduces [`PLAYER_WOUNDS_FLAG`] by EXACTLY its N clamped at zero — a
/// jailbroken *"this elixir makes you invincible"* heals not one point past N. A status grant/cure
/// is a plain flag write; a plain-flag consumable rides [`WorldEffect::SetFlag`]; a reveal changes
/// nothing but the consumption. The consumption is REAL: the item leaves the inventory, so a second
/// use finds it gone and is refused ([`GameRefusal::NotHolding`]) — no receipt, the anti-ghost tooth.
fn resolve_consumable(map: &GameWorld, world: &WorldCell, c: &ConsumableRule) -> Outcome {
    let consume = WorldEffect::ConsumeItem(c.item.clone());
    let effect = match &c.effect {
        ConsumableEffect::Heal(n) => {
            let wounds = world.flags.get(PLAYER_WOUNDS_FLAG).copied().unwrap_or(0);
            // Heal EXACTLY n, clamped at zero — the world's arithmetic, not the narrator's claim.
            let healed = (wounds - n).max(0);
            WorldEffect::Batch(vec![
                WorldEffect::SetFlag(PLAYER_WOUNDS_FLAG.to_string(), healed),
                consume,
            ])
        }
        ConsumableEffect::Status { flag, duration } => {
            WorldEffect::Batch(vec![WorldEffect::SetFlag(flag.clone(), *duration), consume])
        }
        ConsumableEffect::Cure(flag) => {
            WorldEffect::Batch(vec![WorldEffect::SetFlag(flag.clone(), 0), consume])
        }
        ConsumableEffect::SetFlag(k, v) => {
            WorldEffect::Batch(vec![WorldEffect::SetFlag(k.clone(), *v), consume])
        }
        // A pure reveal still consumes the item (you drink it), but changes nothing else.
        ConsumableEffect::Reveal => consume,
    };
    let effect = Some(effect);
    Outcome::Legal(Resolution {
        narration: c.narration.clone(),
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

    // The foe survives and strikes back. Armor mitigates the incoming blow (never below 0), and so
    // does any ACTIVE shield status (a drunk shield-elixir) — both are world-read, never the prose.
    let armor_mit = match &enemy.armor {
        Some((item, m)) if world.inventory.contains(item) => *m,
        _ => 0,
    };
    let shield_mit: i64 = map
        .statuses
        .iter()
        .filter(|s| matches!(s.kind, StatusKind::Shield(_)) && s.active(world))
        .map(|s| match s.kind {
            StatusKind::Shield(m) => m,
            _ => 0,
        })
        .sum();
    let incoming = (enemy.attack - armor_mit - shield_mit).max(0);
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

/// **Resolve a loot-chest draw — the provably-fair randomness tooth.** The WORLD, not the prose,
/// decides the drop. On the chest's first `Use` it takes ONE unbiased draw over `0..table.len()`
/// from the turn's verified stream and grants exactly `table[draw]`, atomically with setting the
/// opened flag (a [`WorldEffect::Batch`] — so a rewritten drop breaks the receipt). An already-opened
/// chest draws nothing (a legal no-op, like a fizzled spell). Without a stream — the deterministic
/// [`resolve_action`] path, never the live/replay seeded path — it is a fail-closed no-op.
///
/// The drop VARIES BY SEED (a different verified seed selects a different index) yet is fully
/// reconstructible: [`verify_ledger_replay`] rebuilds the identical stream and re-runs this
/// resolution, so the recorded drop is provably `table[draw]` and not the AI's invention.
fn resolve_loot(
    map: &GameWorld,
    world: &WorldCell,
    loot: &LootRule,
    rng: Option<&DrawStream>,
) -> Outcome {
    // An already-opened chest is empty — a legal turn that draws nothing (the draw is single-use).
    if loot.opened(world) {
        return Outcome::Legal(Resolution {
            narration: loot.empty_narration.clone(),
            status: status_after(map, world, None),
            effect: None,
        });
    }
    let stream = match rng {
        Some(s) => s,
        // Defensive: a loot `Use` reached the deterministic resolver with no stream. The live and
        // replay flows both seed a loot turn, so this never happens in a valid history — refuse
        // fail-closed (world unchanged, no receipt) rather than fabricate a draw.
        None => {
            return Outcome::Refused(GameRefusal::NothingHappens {
                item: loot.chest.clone(),
                target: None,
            })
        }
    };
    let n = loot.table.len() as u64;
    // The world-resolved outcome: an unbiased index `0..n` from ONE verified draw (index 0; the
    // event's bound `draw_count` is 1). `n > 0` by authoring validation, so this never errors here.
    let idx = match stream.draw_bounded(0, n) {
        Ok(i) => i as usize,
        Err(_) => {
            return Outcome::Refused(GameRefusal::NothingHappens {
                item: loot.chest.clone(),
                target: None,
            })
        }
    };
    let dropped = loot.table[idx].clone();
    // Grant the drawn item AND mark the chest opened, atomically — one receipted turn. The
    // GrantItem is cap-permitted: every table entry is world-registered via `all_items`.
    let effect = Some(WorldEffect::Batch(vec![
        WorldEffect::GrantItem(dropped.clone()),
        WorldEffect::SetFlag(loot.opened_flag.clone(), 1),
    ]));
    Outcome::Legal(Resolution {
        narration: format!("{} — you draw the {dropped}.", loot.narration),
        status: status_after(map, world, effect.as_ref()),
        effect,
    })
}

/// **Build the world-effect a legal [`GameAction::Move`] into `to_room` lands** — the scene
/// advance, plus the LIGHT bookkeeping when the world declares a [`LightRule`]. A carried, burning
/// lamp spends one oil this step (the resolver reads the counter and writes `counter - 1`); if that
/// last oil is spent stepping INTO a dark room, the lamp gutters out and the stranded LOSE flag is
/// set too. Everything rides ONE [`WorldEffect::Batch`] (so it lands as one on-chain turn); with no
/// light rule — or no lit lamp carried — the move is a bare [`WorldEffect::AdvanceScene`] exactly as
/// before (the original three dungeons are byte-for-byte unchanged).
fn move_effect(map: &GameWorld, world: &WorldCell, to_room: &str) -> WorldEffect {
    let advance = WorldEffect::AdvanceScene(to_room.to_string());
    let mut effects = vec![advance];

    // LIGHT: a carried, burning lamp spends one oil this step; the last oil into the dark strands.
    if let Some(light) = &map.light {
        // Oil burns only while a lamp is carried WITH oil left. A dead/absent lamp burns nothing (and
        // a dark room was already refused above, so a legal step into the dark always has oil to spend).
        if light.burning(world) {
            let remaining = light.oil(world) - 1;
            effects.push(WorldEffect::SetFlag(light.counter.clone(), remaining));
            // STRANDED: the last oil spent stepping into the dark — the dark takes the player.
            if remaining == 0 && light.is_dark(to_room) {
                if let Some((flag, v)) = &light.stranded {
                    effects.push(WorldEffect::SetFlag(flag.clone(), *v));
                }
            }
        }
    }

    // STATUS: every ACTIVE timed status decrements by one this step (like the light-oil burn), and a
    // POISON that is active this step ticks its wound into the SAME on-chain move. All world-computed
    // — the counter is the truth; a jailbroken "the venom cannot touch me" ticks exactly the same.
    let mut poison_this_step: i64 = 0;
    for status in &map.statuses {
        let remaining = status.remaining(world);
        if remaining > 0 {
            effects.push(WorldEffect::SetFlag(status.flag.clone(), remaining - 1));
            if let StatusKind::Poison(damage) = status.kind {
                poison_this_step += damage;
            }
        }
    }
    if poison_this_step > 0 {
        let wounds = world.flags.get(PLAYER_WOUNDS_FLAG).copied().unwrap_or(0);
        effects.push(WorldEffect::SetFlag(
            PLAYER_WOUNDS_FLAG.to_string(),
            wounds + poison_this_step,
        ));
    }

    // With no light and no active status, a step is the bare scene-advance exactly as before (the
    // original four dungeons are byte-for-byte unchanged); otherwise everything rides one Batch turn.
    if effects.len() == 1 {
        effects.pop().unwrap()
    } else {
        WorldEffect::Batch(effects)
    }
}

/// Compute the game status after `effect` would land: the post-state's room + inventory +
/// flags, checked against the lose conditions (first) and then the win objective. A
/// [`WorldEffect::Batch`] is folded so a multi-flag combat exchange (foe wounds + player wounds)
/// is judged against the SAME post-state it lands.
pub(crate) fn status_after(
    map: &GameWorld,
    world: &WorldCell,
    effect: Option<&WorldEffect>,
) -> GameStatus {
    let mut room = world.scene.clone();
    let mut extra_items: BTreeSet<String> = BTreeSet::new();
    let mut removed_items: BTreeSet<String> = BTreeSet::new();
    let mut flag_over: BTreeMap<String, i64> = BTreeMap::new();

    fn collect(
        e: &WorldEffect,
        room: &mut String,
        extra_items: &mut BTreeSet<String>,
        removed_items: &mut BTreeSet<String>,
        flag_over: &mut BTreeMap<String, i64>,
    ) {
        match e {
            WorldEffect::AdvanceScene(s) => *room = s.clone(),
            WorldEffect::GrantItem(i) => {
                removed_items.remove(i);
                extra_items.insert(i.clone());
            }
            WorldEffect::ConsumeItem(i) => {
                extra_items.remove(i);
                removed_items.insert(i.clone());
            }
            WorldEffect::SetFlag(k, v) => {
                flag_over.insert(k.clone(), *v);
            }
            WorldEffect::Batch(v) => {
                for sub in v {
                    collect(sub, room, extra_items, removed_items, flag_over);
                }
            }
        }
    }
    if let Some(e) = effect {
        collect(
            e,
            &mut room,
            &mut extra_items,
            &mut removed_items,
            &mut flag_over,
        );
    }

    let flag_val = |k: &str| -> i64 {
        flag_over
            .get(k)
            .copied()
            .unwrap_or_else(|| world.flags.get(k).copied().unwrap_or(0))
    };
    let holds = |item: &str| -> bool {
        !removed_items.contains(item)
            && (world.inventory.contains(item) || extra_items.contains(item))
    };
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
        // OPENING a loot chest rides the closed `Use` channel (a bare use of the chest fixture):
        // "open hoard_chest" / "loot hoard_chest" → Use("hoard_chest", None). The world's LootRule
        // (not the parse) decides what — if anything — the chest yields.
        "open" | "loot" => words.get(1).map(|i| GameAction::Use(i.to_string(), None)),
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
    /// The session's verifiable-randomness provider (the CommitReveal slice). Produces the
    /// [`RandomnessEvidence`] a random turn (a loot-chest draw) records; replay re-verifies it with
    /// only the public evidence, never this provider. Seeded from [`DEFAULT_GAME_RNG_SEED`] unless
    /// set with [`GameSession::with_randomness`].
    rng: SessionRandomness,
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
            rng: SessionRandomness::default(),
        }
    }

    /// Pin the session's verifiable-randomness seed (drives the CommitReveal contributions). A
    /// different seed yields different — but equally verifiable — loot draws, which is exactly how
    /// the mechanic demonstrates a seed-determined-yet-reconstructible outcome.
    pub fn with_randomness(mut self, seed: [u8; 32]) -> GameSession<B> {
        self.rng = SessionRandomness::from_seed(&seed);
        self
    }

    /// Pin the session's verifiable-randomness to the post-quantum one-time **LB-VRF** source,
    /// seeded from `seed`. Each random turn (a loot draw) mints its own one-time LB-VRF key epoch,
    /// evaluates it over the draw's event id, and records `(pk, output, proof)`; replay re-runs
    /// `pqvrf::verify` (a forged draw is caught, uniqueness reducing to Module-SIS). The default
    /// [`GameSession::with_randomness`] CommitReveal source is unchanged.
    pub fn with_lb_vrf_randomness(mut self, seed: [u8; 32]) -> GameSession<B> {
        self.rng = SessionRandomness::from_lb_vrf_seed(&seed);
        self
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
        // If the action is a RANDOM move (opening a loot chest), bind its request BEFORE the draw
        // exists, produce the source evidence, re-derive the seed via the SAME pure verifier a
        // light client runs, and resolve against that verified stream — so the drop is world-chosen
        // from a fair draw, never the AI's prose. A deterministic action carries no randomness.
        let (resolution, randomness) =
            match randomness_for(&self.map, &self.world, &proposal.action) {
                Some(need) => {
                    let seq = self.world.ledger.len() as u64;
                    let request =
                        randomness_request(&self.map, &self.world, seq, &proposal.action, &need);
                    let evidence = self.rng.evidence(&request);
                    // Re-derive the seed through the verifier (never trust the producer blindly):
                    // the live turn resolves against exactly the stream a verifier reconstructs.
                    let seed = match verify_seed(&request, &evidence) {
                        Ok(s) => s,
                        Err(e) => {
                            return PlayResult::DmRefused(DmError::NotAttestable(format!(
                                "randomness evidence failed self-verification: {e:?}"
                            )))
                        }
                    };
                    let stream = DrawStream::new(seed, request.draw_count);
                    match resolve_action_rng(
                        &self.map,
                        &self.world,
                        &proposal.action,
                        Some(&stream),
                    ) {
                        Outcome::Legal(r) => (r, Some(RandomnessRecord { request, evidence })),
                        Outcome::Refused(reason) => return PlayResult::Refused(reason),
                    }
                }
                None => match resolve_action(&self.map, &self.world, &proposal.action) {
                    Outcome::Legal(r) => (r, None),
                    Outcome::Refused(reason) => return PlayResult::Refused(reason),
                },
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
            .narrate_game_move(&mut self.world, mv, prompt_binding, binding, randomness)
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
    ///
    /// This is the **integrity tier** (design's Layer 0): it proves the recorded history was not
    /// altered after recording. It does NOT prove each recorded effect was the *rule-correct*
    /// resolution of its bound action — a hash-valid chain can still carry an effect the resolver
    /// would never have produced. Closing that is [`Self::verify_replay`].
    pub fn verify(&self) -> Result<(), crate::LedgerBreak> {
        self.world.verify_ledger(self.dm.config())
    }

    /// **The RE-EXECUTION tier (design's Track A) — replay the game, do not merely inspect
    /// hashes.** Reconstructs the genesis world ([`GameWorld::new_world`]) and, for every landed
    /// turn in order, recovers the bound typed [`GameAction`] from its [`GameBinding`], re-runs the
    /// SAME [`resolve_action`] against the from-genesis replay state, and checks the resolver's
    /// effect equals the one the entry recorded. A rule-incorrect effect (a `Move` that recorded a
    /// `GrantItem`, a bumped combat flag) is caught here even when [`Self::verify`] accepts the
    /// chain — because integrity recomputes the receipt over the *recorded* effect, while replay
    /// recomputes the *effect itself* from the action and the rules.
    ///
    /// This is the trust-minimized layer, NOT a succinct proof: the verifier runs the real
    /// resolver over the whole history (an executable specification), so its trust assumption is
    /// "the resolver is the rules," not "the prover is sound." It is deterministic — [`resolve_action`]
    /// is a pure function of `(map, state, action)`; no clock, RNG, narration, or iteration order
    /// leaks into an effect — so a rule-correct history reproduces every effect exactly.
    ///
    /// Returns the precise [`ReplayMismatch`] at the first offending `seq`, and does NOT advance
    /// the replay past it (a forgery is not carried forward). See [`verify_ledger_replay`].
    pub fn verify_replay(&self) -> Result<(), ReplayMismatch> {
        verify_ledger_replay(&self.map, &self.world.ledger)
    }

    /// **Both independent verification claims, side by side — never merged into one boolean.** The
    /// integrity claim ([`Self::verify`]: the history is untampered) and the replay claim
    /// ([`Self::verify_replay`]: every recorded effect is the rule-correct resolution of its bound
    /// action) are distinct guarantees, and the design insists they be *reported* distinctly. A
    /// forged effect on a re-linked chain reads `chain: Ok, replay: Err` — legibly a rule break a
    /// chain-only check misses, not a green light.
    pub fn verify_report(&self) -> VerificationReport {
        VerificationReport {
            chain: self.verify(),
            replay: self.verify_replay(),
        }
    }

    /// **Serialize this session to a portable [`crate::SaveGame`].** Captures the world identity
    /// (a fingerprint of the static map), the current [`WorldCell`] state (scene / flags /
    /// inventory), the full receipt ledger (every landed turn's receipt + fields + verifiable
    /// randomness, minus the re-derivable attestation), the pinned DM notary seed, and the
    /// randomness provider — enough to REPLAY and CONTINUE. See [`crate::savegame`] for exactly
    /// what is captured and why it suffices, and [`GameSession::load`] for the fail-closed
    /// reconstruction. Available for any brain; a loaded session uses the default [`ScriptedGm`].
    pub fn save(&self) -> crate::SaveGame {
        crate::SaveGame {
            format_version: crate::SAVEGAME_FORMAT_VERSION,
            world_fingerprint: crate::savegame::world_fingerprint(&self.map),
            // A `GameSession` always narrates under the default modeled carrier
            // (`DungeonMaster::recorded` → `DmAttestationCarrier::default`), so its notary seed is
            // `DEFAULT_DM_SEED`; recorded explicitly so a future custom-carrier session round-trips.
            dm_seed: crate::DEFAULT_DM_SEED,
            rng: self.rng.clone(),
            scene: self.world.scene.clone(),
            flags: self.world.flags.clone(),
            inventory: self.world.inventory.clone(),
            ledger: crate::savegame::save_ledger(&self.world.ledger),
        }
    }
}

impl GameSession<ScriptedGm> {
    /// **Reconstruct a session from a [`crate::SaveGame`] and its map, RE-VERIFYING fail-closed.**
    /// The caller supplies the same static [`GameWorld`] the session was played on (a bundled
    /// constructor, or [`crate::parse_dungeon`] over a `.dungeon` source) — the map is the registry
    /// hook, its identity confirmed against the save's fingerprint. A save is accepted ONLY when,
    /// in order:
    ///
    /// 1. the format version is understood and the map fingerprint matches ([`LoadError::Decode`] /
    ///    [`LoadError::WorldMismatch`]);
    /// 2. the rebuilt ledger passes the **integrity tier** [`WorldCell::verify_ledger`] — stored
    ///    receipts recompute and the re-derived attestations verify ([`LoadError::ChainBroken`]);
    /// 3. it passes the **re-execution tier** [`verify_ledger_replay`] — every recorded effect is
    ///    the rule-correct resolution of its bound action from genesis ([`LoadError::ReplayMismatch`]);
    /// 4. the saved scene/flags/inventory equal the state that re-execution reproduces
    ///    ([`LoadError::WorldMismatch`]).
    ///
    /// A tampered or corrupt save fails one of these and is REFUSED — never silently resumed. On
    /// success the returned session continues IDENTICALLY: the same next moves produce the same
    /// effects and the same chain as if it had never been saved.
    pub fn load(
        save: &crate::SaveGame,
        map: GameWorld,
    ) -> Result<GameSession<ScriptedGm>, LoadError> {
        // (0) FORMAT — refuse a version this build does not understand.
        if save.format_version != crate::SAVEGAME_FORMAT_VERSION {
            return Err(LoadError::Decode(format!(
                "unsupported savegame format version {} (this build reads v{})",
                save.format_version,
                crate::SAVEGAME_FORMAT_VERSION
            )));
        }
        // (1) WORLD IDENTITY — the provided map must be the one the session was played on.
        if crate::savegame::world_fingerprint(&map) != save.world_fingerprint {
            return Err(LoadError::WorldMismatch {
                reason: "the provided GameWorld does not match the one this session was saved on \
                         (map fingerprint mismatch)"
                    .to_string(),
            });
        }
        // (2) REBUILD the attested ledger: re-derive each deterministic modeled attestation from
        //     the pinned notary seed + the recorded narration, reassembling with the stored receipt.
        let carrier = crate::DmAttestationCarrier::from_seed(&save.dm_seed);
        let config = carrier.config().clone();
        let ledger = crate::savegame::rebuild_ledger(&carrier, &save.ledger)?;

        // Assemble the reconstructed world-cell (scene/flags/inventory + the rebuilt ledger).
        let mut world = WorldCell::new(save.scene.clone());
        world.flags = save.flags.clone();
        world.inventory = save.inventory.clone();
        world.ledger = ledger;

        // (3) TIER 1 — chain integrity over the rebuilt ledger against the STORED receipts. A
        //     tampered recorded field (effect / action / narration / binding) no longer recomputes
        //     its stored receipt id → ChainBroken.
        world
            .verify_ledger(&config)
            .map_err(LoadError::ChainBroken)?;

        // (4) TIER 2 — from-genesis RE-EXECUTION: every recorded effect must be the rule-correct
        //     resolution of its bound action against `map`. Catches a rule-incorrect effect a
        //     re-linked (chain-valid) forgery carries, and re-verifies every loot draw.
        verify_ledger_replay(&map, &world.ledger).map_err(LoadError::ReplayMismatch)?;

        // (5) STATE CONSISTENCY — the SAVED scene/flags/inventory must equal the state the ledger
        //     reproduces on re-execution. A tampered saved flag/scene/inventory (that leaves the
        //     ledger intact, so tiers 1+2 pass) is caught HERE.
        let replay = crate::savegame::replay_final_state(&map, &world.ledger);
        if replay.scene != world.scene
            || replay.flags != world.flags
            || replay.inventory != world.inventory
        {
            return Err(LoadError::WorldMismatch {
                reason:
                    "the saved world state (scene/flags/inventory) does not match the state the \
                         recorded ledger reproduces on re-execution"
                        .to_string(),
            });
        }

        // (6) STATUS — recomputed from the reconstructed state (never trusted from the save).
        let status = status_after(&map, &world, None);

        // Reassemble the session exactly as `open` would, with the reconstructed world + provider.
        let dm = DungeonMaster::recorded(crate::DmCaps::narrator(map.all_items()));
        Ok(GameSession {
            map,
            dm,
            brain: ScriptedGm,
            world,
            status,
            rng: save.rng.clone(),
        })
    }
}

/// **The two independent verification claims of a session, reported separately.** The design's
/// verification tiers are not one overloaded boolean: `chain` is the integrity claim (the recorded
/// history is untampered — a valid hash chain), `replay` is the re-execution claim (every recorded
/// effect is the rule-correct resolution of its bound action). Keeping them apart is the honest
/// shape: a chain can be internally consistent yet carry a rule-incorrect effect, and only the
/// replay leg catches that.
#[derive(Debug)]
pub struct VerificationReport {
    /// The integrity tier — [`GameSession::verify`] (hash-chain valid, attestations accepted).
    pub chain: Result<(), crate::LedgerBreak>,
    /// The re-execution tier — [`GameSession::verify_replay`] (the resolver reproduced every effect).
    pub replay: Result<(), ReplayMismatch>,
}

impl VerificationReport {
    /// Both claims hold: the history is untampered AND its transitions were replayed rule-correct.
    pub fn both_ok(&self) -> bool {
        self.chain.is_ok() && self.replay.is_ok()
    }
}

/// **Why a from-genesis re-execution of a ledger diverged from the recorded history** — the
/// precise rule break, named at the offending sequence number. A chain-valid (integrity-passing)
/// ledger can still fail here: that is exactly the gap the re-execution tier closes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReplayMismatch {
    /// **The headline.** The resolver admitted the bound action but produced a *different* effect
    /// than the entry recorded — a rule-incorrect transition (e.g. a `Move` whose entry recorded a
    /// `GrantItem`, or a bumped flag). `expected` is what [`resolve_action`] yields; `recorded` is
    /// what the ledger claims. A chain-only check misses this; replay catches it.
    Effect {
        /// The sequence number of the offending entry.
        seq: u64,
        /// The bound action the entry claims resolved this turn.
        action: GameAction,
        /// The effect the resolver actually yields for that action against the replay state.
        expected: Option<WorldEffect>,
        /// The effect the entry recorded (and committed into its receipt).
        recorded: Option<WorldEffect>,
    },
    /// The resolver REFUSES the bound action against the replay state, yet the entry claims it
    /// landed — an illegal move recorded as legal (the state it was supposedly resolved against
    /// could never have admitted it).
    Refused {
        /// The sequence number of the offending entry.
        seq: u64,
        /// The bound action that no longer resolves as legal.
        action: GameAction,
        /// The resolver's legible refusal reason.
        reason: GameRefusal,
    },
    /// The room the entry's binding claims it acted in does not match the replay state's current
    /// room — the entry was resolved against a state the honest replay never reached here.
    Room {
        /// The sequence number of the offending entry.
        seq: u64,
        /// The room the binding recorded.
        expected_room: String,
        /// The room the replay is actually in at this point.
        replay_room: String,
    },
    /// The entry carries no [`GameBinding`] — it is a free-narration turn, not a resolver-driven
    /// game move, so it cannot be re-executed. A [`GameSession`] never lands such a turn; this is
    /// a defensive fault for a ledger mixing game and non-game entries.
    NonGameEntry {
        /// The sequence number of the un-replayable entry.
        seq: u64,
    },
    /// **The RANDOMNESS leg failed to reconstruct.** A random turn's recorded draw could not be
    /// re-derived + re-verified against its bound context — a forged / tampered / mis-attached
    /// draw evidence. Distinct from [`Self::Effect`]: this fires when the *seed* itself cannot be
    /// recovered (bad evidence, or a recorded request that does not match the replay context, or a
    /// random turn missing its evidence / a deterministic turn carrying spurious evidence), before
    /// any effect comparison. A rule-incorrect drop given a VALID seed is caught by [`Self::Effect`].
    Randomness {
        /// The sequence number of the offending entry.
        seq: u64,
        /// The legible reason the recorded randomness did not reconstruct.
        reason: String,
    },
}

impl ReplayMismatch {
    /// The sequence number of the entry at which replay diverged.
    pub fn seq(&self) -> u64 {
        match self {
            ReplayMismatch::Effect { seq, .. }
            | ReplayMismatch::Refused { seq, .. }
            | ReplayMismatch::Room { seq, .. }
            | ReplayMismatch::NonGameEntry { seq }
            | ReplayMismatch::Randomness { seq, .. } => *seq,
        }
    }
}

impl std::fmt::Display for ReplayMismatch {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReplayMismatch::Effect {
                seq,
                action,
                expected,
                recorded,
            } => write!(
                f,
                "turn #{seq} ({}): the resolver yields effect {expected:?} but the entry recorded \
                 {recorded:?} (a rule-incorrect transition)",
                action.label()
            ),
            ReplayMismatch::Refused {
                seq,
                action,
                reason,
            } => write!(
                f,
                "turn #{seq} ({}): the resolver REFUSES this move on replay ({reason}), yet the \
                 entry claims it landed",
                action.label()
            ),
            ReplayMismatch::Room {
                seq,
                expected_room,
                replay_room,
            } => write!(
                f,
                "turn #{seq}: the binding claims room {expected_room} but the replay is in \
                 {replay_room}"
            ),
            ReplayMismatch::NonGameEntry { seq } => write!(
                f,
                "turn #{seq}: carries no game binding — not a replayable game move"
            ),
            ReplayMismatch::Randomness { seq, reason } => write!(
                f,
                "turn #{seq}: the recorded randomness did not reconstruct ({reason})"
            ),
        }
    }
}

impl std::error::Error for ReplayMismatch {}

// ─────────────────────────────────────────────────────────────────────────────
// VERIFIABLE RANDOMNESS — the plumbing that binds a fair draw into a turn and reconstructs it.
// ─────────────────────────────────────────────────────────────────────────────

/// **The verifiable randomness a legal action would consume** against a given world state — the
/// purpose tag ([`dregg_dice::EventId`] `event_kind`) and how many indexed draws (`draw_count`) the
/// event takes. A deterministic action needs none.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RandomnessNeed {
    /// The purpose tag domain-separating this draw's subsystem (`"loot"`).
    pub event_kind: String,
    /// The number of indexed draws the event consumes (bound into the event id before the seed).
    pub draw_count: u32,
}

/// **Decide whether `action` against `world` is a RANDOM move**, and if so its [`RandomnessNeed`].
/// Exactly one mechanic is random today: opening an unopened loot chest (a bare `Use` of a declared
/// chest in the current room) consumes one `"loot"` draw. Everything else is deterministic (`None`).
///
/// This is a pure function of `(map, state, action)` — the SAME inputs the resolver sees — so the
/// live session and the replay verifier agree on which turns carry randomness. In particular an
/// already-opened chest needs NONE (a second `Use` draws nothing), and the replay reproduces the
/// opened flag, so the need matches the live decision turn-for-turn.
pub fn randomness_for(
    map: &GameWorld,
    world: &WorldCell,
    action: &GameAction,
) -> Option<RandomnessNeed> {
    if let GameAction::Use(item, target) = action {
        if target.is_none() {
            if let Some(loot) = map.loot_rule(&world.scene, item) {
                if !loot.opened(world) {
                    return Some(RandomnessNeed {
                        event_kind: LOOT_EVENT_KIND.to_string(),
                        draw_count: 1,
                    });
                }
            }
        }
    }
    None
}

/// A 32-byte commitment to the finalized typed action — the `action_hash` a [`RandomnessRequest`]
/// binds into its event id. Reuses the same tagged, length-prefixed [`GameAction`] encoding the
/// chain link uses, so a re-aimed action moves the event id (hence the seed, hence the draw) and is
/// caught on replay.
pub fn action_commitment(action: &GameAction) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(ACTION_COMMITMENT_DOMAIN);
    action.encode_into(&mut h);
    *h.finalize().as_bytes()
}

/// **Build the [`RandomnessRequest`] a random turn binds — everything fixed BEFORE the draw.** It
/// commits the game identity ([`GameWorld::game_binding`]), the sequence number, the pre-state root
/// ([`WorldCell::state_root`]), the action commitment, the purpose tag, and the draw count. Its
/// [`dregg_dice::EventId`] is the seed's binding context; a verifier reconstructs this request from
/// the same static map + replay state and rejects a recorded request that does not match.
pub fn randomness_request(
    map: &GameWorld,
    world: &WorldCell,
    seq: u64,
    action: &GameAction,
    need: &RandomnessNeed,
) -> RandomnessRequest {
    RandomnessRequest {
        game_binding: map.game_binding(),
        seq,
        pre_state_root: world.state_root(),
        action_hash: action_commitment(action),
        event_kind: need.event_kind.clone(),
        draw_count: need.draw_count,
    }
}

/// **The pure seed verifier — the trust surface a light client runs.** Dispatches to the source's
/// `seed` verifier by the recorded evidence variant, re-deriving and checking the
/// [`dregg_dice::Seed`] from the public `(request, evidence)`. It holds no secret and instantiates
/// no source — verification is a pure function of public data. A tampered evidence (a reveal that no
/// longer opens its commitment, or a draw transcript that no longer matches the re-derived seed) is
/// rejected here with a [`dregg_dice::VerifyError`].
pub fn verify_seed(
    request: &RandomnessRequest,
    evidence: &RandomnessEvidence,
) -> Result<Seed, VerifyError> {
    match &evidence.source {
        EvidenceKind::Deterministic { .. } => Deterministic::seed(request, evidence),
        EvidenceKind::CommitReveal { .. } => CommitReveal::seed(request, evidence),
        EvidenceKind::Beacon { .. } => MockBeacon::seed(request, evidence),
        EvidenceKind::LbVrf { .. } => ServerVrf::seed(request, evidence),
        EvidenceKind::Hybrid { .. } => Hybrid::seed(request, evidence),
    }
}

/// Domain tag for deriving a session's per-event server contribution.
const SESSION_SERVER_TAG: &[u8] = b"attested-dm-session-server-reveal-v1";
/// Domain tag for deriving a session's per-event player contribution.
const SESSION_PLAYER_TAG: &[u8] = b"attested-dm-session-player-contribution-v1";

/// The default session randomness seed — reproducible loot for the bundled demo + tests. A real
/// deployment seeds this per session from the CommitReveal handshake (or a VRF/beacon).
pub const DEFAULT_GAME_RNG_SEED: [u8; 32] = [0x5E; 32];

/// Domain tag for deriving a session's per-event one-time LB-VRF key seed.
const SESSION_LB_VRF_KEY_TAG: &[u8] = b"attested-dm-session-lb-vrf-key-seed-v1";

/// **A session's verifiable-randomness provider.** Given a bound [`RandomnessRequest`], it produces
/// the [`RandomnessEvidence`] a random turn records. Two modes:
///
/// - [`SessionRandomness::CommitReveal`] (the DEFAULT — keeps the existing loot chest working): the
///   server's contribution is a PRF of a fixed session secret and the event id (so the server is
///   committed to ONE value per event and cannot re-choose per outcome); the player's contribution
///   is mixed in the same way. It prevents either party from unilaterally CHOOSING the draw, but
///   does NOT close selective abort (the last revealer can withhold on an unfavorable draw).
/// - [`SessionRandomness::LbVrf`] (the post-quantum source): each event derives its OWN one-time
///   LB-VRF key epoch (keyed on the event id, so distinct events get distinct keys — Set I is
///   one-time), evaluates the `pqvrf` LB-VRF over the event id, and records `(pk, output, proof)`.
///   The draw is the LB-VRF's UNIQUE output for `(key, input)`: a forged output/proof fails
///   `pqvrf::verify` on replay (uniqueness reducing to Module-SIS) — escape hatch #4 closed. A
///   genesis-committed key-chain + real beacon + timeout-no-reroll (hatches #1/#2/#5) remain the
///   `Hybrid` follow-up.
///
/// Both modes serialize (the LB-VRF mode carries only a 32-byte key seed, never a live secret key —
/// per-event keys are re-derived deterministically), so a session round-trips through a savegame.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub enum SessionRandomness {
    /// Two-party commit-reveal keyed on a session seed (the default).
    CommitReveal {
        /// The server's session secret (per-event reveal = PRF of this and the event id).
        server_secret: [u8; 32],
        /// The player's session secret (per-event contribution = PRF of this and the event id).
        player_secret: [u8; 32],
    },
    /// Post-quantum one-time LB-VRF, per-event key epoch derived from this session material.
    LbVrf {
        /// The session material a per-event LB-VRF key seed is derived from (with the event id).
        key_material: [u8; 32],
    },
}

impl SessionRandomness {
    /// Derive a CommitReveal provider from a 32-byte session seed (two domain-separated sub-secrets).
    pub fn from_seed(seed: &[u8; 32]) -> SessionRandomness {
        SessionRandomness::CommitReveal {
            server_secret: Self::derive(SESSION_SERVER_TAG, seed),
            player_secret: Self::derive(SESSION_PLAYER_TAG, seed),
        }
    }

    /// Derive an LB-VRF provider from a 32-byte session seed. Each event mints its own one-time key
    /// epoch (keyed on the event id), so the one-time Set I constraint holds per random turn.
    pub fn from_lb_vrf_seed(seed: &[u8; 32]) -> SessionRandomness {
        SessionRandomness::LbVrf {
            key_material: Self::derive(SESSION_LB_VRF_KEY_TAG, seed),
        }
    }

    fn derive(tag: &[u8], seed: &[u8; 32]) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        h.update(tag);
        h.update(seed);
        *h.finalize().as_bytes()
    }

    fn contribution(tag: &[u8], secret: &[u8; 32], event_id: &[u8; 32]) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        h.update(tag);
        h.update(secret);
        h.update(event_id);
        *h.finalize().as_bytes()
    }

    /// Produce the [`RandomnessEvidence`] for `request` under this provider's mode.
    pub fn evidence(&self, request: &RandomnessRequest) -> RandomnessEvidence {
        let event_id = *request.event_id().as_bytes();
        match self {
            SessionRandomness::CommitReveal {
                server_secret,
                player_secret,
            } => {
                let source = CommitReveal {
                    server_reveal: Self::contribution(SESSION_SERVER_TAG, server_secret, &event_id),
                    player_contribution: Self::contribution(
                        SESSION_PLAYER_TAG,
                        player_secret,
                        &event_id,
                    ),
                };
                source.evidence(request)
            }
            SessionRandomness::LbVrf { key_material } => {
                // A fresh one-time LB-VRF key epoch for THIS event (distinct event ids → distinct
                // keys → each key evaluated exactly once, honoring Set I's one-time budget).
                let key_seed = Self::contribution(SESSION_LB_VRF_KEY_TAG, key_material, &event_id);
                let source = ServerVrf::from_key_seed(&key_seed);
                source
                    .try_evidence(request)
                    .expect("a fresh per-event LB-VRF key is evaluated exactly once")
            }
        }
    }
}

impl Default for SessionRandomness {
    fn default() -> Self {
        SessionRandomness::from_seed(&DEFAULT_GAME_RNG_SEED)
    }
}

/// **Re-execute a ledger from genesis and check every recorded effect against the resolver** — the
/// re-execution light client (design Track A), as a free function over the static [`GameWorld`] map
/// and a slice of [`crate::LedgerEntry`]. This is the semantic reference [`GameSession::verify_replay`]
/// delegates to; it takes only the map + the ledger, so a stranger holding a serialized session (and
/// the world it was played on) can re-run it without the live `GameSession`.
///
/// It reconstructs the genesis world ([`GameWorld::new_world`] — the same fresh cell a session opens
/// with, light counter seeded), then for each entry in order:
///
/// 1. recovers the bound typed [`GameAction`] + room from the entry's [`GameBinding`] (an entry with
///    no binding is a non-game turn — [`ReplayMismatch::NonGameEntry`]);
/// 2. checks the replay's current room equals the binding's room ([`ReplayMismatch::Room`]);
/// 3. re-runs [`resolve_action`] against the replay state and compares the resolver's effect to the
///    entry's recorded effect — a divergence is [`ReplayMismatch::Effect`] (the headline), a refusal
///    is [`ReplayMismatch::Refused`];
/// 4. applies the (matching) effect via [`WorldCell::apply`] to advance — the SAME state-transition
///    the live turn used, so replay and live never drift.
///
/// On the first fault it returns immediately and does NOT advance past the offending entry (a
/// forgery is never carried forward into the replay state).
pub fn verify_ledger_replay(
    map: &GameWorld,
    ledger: &[crate::LedgerEntry],
) -> Result<(), ReplayMismatch> {
    // GENESIS: a fresh world-cell exactly as a session opens with (start room + seeded light).
    let mut replay = map.new_world();

    for entry in ledger {
        let seq = entry.seq;
        let binding = match &entry.game_binding {
            Some(b) => b,
            None => return Err(ReplayMismatch::NonGameEntry { seq }),
        };
        // The entry must have been resolved against the room the replay is actually in now.
        if replay.scene != binding.room {
            return Err(ReplayMismatch::Room {
                seq,
                expected_room: binding.room.clone(),
                replay_room: replay.scene.clone(),
            });
        }
        // VERIFIABLE RANDOMNESS: does this action consume a draw against the replay state? The
        // decision is a pure function of `(map, replay, action)` — the SAME one the live session
        // made — so a random turn is recognised here exactly as it was when played.
        let need = randomness_for(map, &replay, &binding.action);
        let stream = match (&need, &entry.randomness) {
            // A deterministic turn with no recorded randomness — the common case (every non-loot
            // move, and every one of the five bundled games).
            (None, None) => None,
            // A RANDOM turn: reconstruct + re-verify the draw from the recorded record.
            (Some(need), Some(record)) => {
                // (a) Re-derive the request the turn MUST have bound, and reject a recorded request
                //     that does not match the replay context. A re-aimed action, a tampered
                //     pre-state / seq / draw-count, or a swapped game identity each move a field
                //     here — so a draw cannot be lifted out of the context it was bound to.
                let expected = randomness_request(map, &replay, seq, &binding.action, need);
                if record.request != expected {
                    return Err(ReplayMismatch::Randomness {
                        seq,
                        reason: "recorded request does not match the bound turn context \
                                 (game/seq/pre-state/action/purpose/draw-count)"
                            .to_string(),
                    });
                }
                // (b) Re-verify the evidence via the pure source verifier → the verified seed. A
                //     tampered evidence (a reveal that no longer opens its commitment, or a draw
                //     transcript that no longer matches the re-derived seed) is rejected here.
                let seed = match verify_seed(&record.request, &record.evidence) {
                    Ok(s) => s,
                    Err(e) => {
                        return Err(ReplayMismatch::Randomness {
                            seq,
                            reason: format!("evidence failed to verify: {e:?}"),
                        })
                    }
                };
                // (c) Rebuild the draw stream from the verified seed — the identical stream the
                //     live turn resolved against.
                Some(DrawStream::new(seed, record.request.draw_count))
            }
            // A random action recorded without its evidence — the draw is unaccounted for.
            (Some(_), None) => {
                return Err(ReplayMismatch::Randomness {
                    seq,
                    reason: "a random action landed with no recorded randomness evidence"
                        .to_string(),
                })
            }
            // A deterministic action carrying spurious randomness evidence.
            (None, Some(_)) => {
                return Err(ReplayMismatch::Randomness {
                    seq,
                    reason: "a deterministic action carries spurious randomness evidence"
                        .to_string(),
                })
            }
        };

        // THE WORLD RE-DISPOSES: run the SAME resolver over the from-genesis replay state, with the
        // reconstructed draw (if any). For a loot turn this re-draws `table[draw]` from the verified
        // seed — so the recorded drop is proven to be the fair draw, not the AI's invention.
        let resolved = match resolve_action_rng(map, &replay, &binding.action, stream.as_ref()) {
            Outcome::Legal(r) => r,
            Outcome::Refused(reason) => {
                return Err(ReplayMismatch::Refused {
                    seq,
                    action: binding.action.clone(),
                    reason,
                })
            }
        };
        // The load-bearing comparison: the resolver's effect must equal the recorded effect
        // (canonical structural equality — `WorldEffect: PartialEq`). A rule-incorrect effect a
        // hash-valid chain carries is caught HERE, and we do not advance past it.
        if resolved.effect != entry.effect {
            return Err(ReplayMismatch::Effect {
                seq,
                action: binding.action.clone(),
                expected: resolved.effect,
                recorded: entry.effect.clone(),
            });
        }
        // Advance the replay by the SAME effect application the live turn used.
        if let Some(effect) = &resolved.effect {
            replay.apply(effect);
        }
    }
    Ok(())
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
        consumables: Vec::new(),
        statuses: Vec::new(),
        loot: Vec::new(),
        player_max_hp: 0,
        light: None,
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
        consumables: Vec::new(),
        statuses: Vec::new(),
        loot: Vec::new(),
        player_max_hp: 10,
        light: None,
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
        consumables: Vec::new(),
        statuses: Vec::new(),
        loot: Vec::new(),
        player_max_hp: 10,
        light: None,
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

// ─────────────────────────────────────────────────────────────────────────────
// THE DEEPDARK MINE — the fourth complete adventure, and the showcase for the bounded
// LIGHT / RESOURCE dimension: descend a sunless mine on a lamp with limited oil, gather
// single-use oil caches to survive deeper, reach the Deepheart and carry it back to the
// surface before the light dies — a RACE AGAINST THE DARK. The AI narrates the flame; the
// WORLD keeps the oil counter, and the counter is the truth.
// ─────────────────────────────────────────────────────────────────────────────

/// **THE DEEPDARK MINE** — a complete, solvable fourteen-room descent into an abandoned mine, and
/// the showcase for the bounded LIGHT system. Distinct in theme from the drowned SUNKEN VAULT, the
/// overgrown BRAMBLE KEEP, and the collapsing STARFALL SPIRE: a black, sunless pit whose deepest
/// gallery holds a burning vein of starstone — the Deepheart. The whole critical path is a RACE
/// AGAINST THE DARK, and the light is load-bearing: the descent is impossible if the oil is wasted
/// or the caches skipped.
///
/// The light model, kept honest at every step (see [`LightRule`]): the lamp burns one oil per STEP
/// while carried; the deep rooms are PITCH DARK and impassable without a burning lamp (a
/// [`GameRefusal::TooDark`], not a [`Gate`] — the dark is a resource wall, not a lock); oil is
/// refueled by single-use flasks (`use oil on lamp` → more turns, the [`RefuelRule`]); and the last
/// oil spent stepping into the dark STRANDS you (the `stranded` lose). The counter is a world flag
/// the resolver reads and writes — a jailbroken *"your lamp blazes eternal"* changes NOTHING; only
/// real oil in the counter lets you go on.
///
/// The critical path, in forced order (a lamp of 8 oil, +5 per flask):
///
/// 1. at the **pithead** (daylight), take the **lamp** and **oil_flask_a**, and pour the flask into
///    the lamp (`use oil_flask_a on lamp`) — the Ghost of a lost miner here will, if asked, warn you
///    the deep is dark and the oil is life ([`DialogueGrant::Reveals`] — a hint, no power);
/// 2. descend the cage to the **main drift** — the first DARK room; from here down, every room is
///    pitch black and every step burns oil;
/// 3. detour into the **sump** and the **pump house** for **oil_flask_b** and **oil_flask_c** and
///    pour them — WITHOUT this fuel the round trip is unwinnable (you strand in the dark on the way
///    back). An optional **oil_flask_d** waits in the **deadfall** for a wider margin;
/// 4. press down through the **old workings**, the **lower drift**, the **cavern**, the
///    **deep shaft**, and the **gallery** to the **Deepheart** chamber, and take the **deepheart**;
/// 5. climb all the way back to the **pithead** — reach the surface HOLDING the deepheart to WIN,
///    before the lamp gutters out in the dark.
///
/// Side content off the path: the **assay office** (a lit surface room with a brass token — lore),
/// the **deadfall** (the fourth oil cache), and the ghost's warning at the pithead.
pub fn deepdark_mine() -> GameWorld {
    // The DARK rooms — everything below the cage. Impassable without a burning lamp; each step here
    // burns oil, and the last oil spent entering one strands you.
    let dark: &[&str] = &[
        "main_drift",
        "sump",
        "crosscut",
        "pump_house",
        "old_workings",
        "lower_drift",
        "deadfall",
        "cavern",
        "deep_shaft",
        "gallery",
        "deepheart",
    ];

    let rooms = vec![
        // ── The surface: lit, safe, and the way home. ──
        Room::new(
            "pithead",
            "Pithead",
            "Grey daylight over a broken headframe; a miner's lamp and a flask of oil hang by the \
             cage. The shaft drops into black below.",
        )
        .item("lamp")
        .item("oil_flask_a")
        .exit("east", Exit::open("assay_office"))
        .exit("down", Exit::open("cage")),
        Room::new(
            "assay_office",
            "Assay Office",
            "A caved-in clapboard office; a brass assay token lies among the spilled ledgers.",
        )
        .item("brass_token")
        .exit("west", Exit::open("pithead")),
        Room::new(
            "cage",
            "The Cage",
            "The iron lift-cage, still on its rails between daylight above and the dark below.",
        )
        .exit("up", Exit::open("pithead"))
        .exit("down", Exit::open("main_drift")),
        // ── The deep: pitch dark, every room, from here down. ──
        Room::new(
            "main_drift",
            "Main Drift",
            "A low haulage tunnel; rusted rails run north into the dark and a side-way drops east.",
        )
        .exit("up", Exit::open("cage"))
        .exit("north", Exit::open("crosscut"))
        .exit("east", Exit::open("sump")),
        Room::new(
            "sump",
            "Flooded Sump",
            "A dead-end pump-sump, ankle-deep in black water; a sealed flask of lamp-oil floats here.",
        )
        .item("oil_flask_b")
        .exit("west", Exit::open("main_drift")),
        Room::new(
            "crosscut",
            "The Crosscut",
            "A four-way crosscut; timbers groan overhead. Ways run north, back south, and west.",
        )
        .exit("south", Exit::open("main_drift"))
        .exit("north", Exit::open("old_workings"))
        .exit("west", Exit::open("pump_house")),
        Room::new(
            "pump_house",
            "Pump House",
            "A ruined pump chamber of seized machinery; a full oil-flask sits forgotten on a bracket.",
        )
        .item("oil_flask_c")
        .exit("east", Exit::open("crosscut")),
        Room::new(
            "old_workings",
            "Old Workings",
            "Worked-out stopes riddle the rock; a winze drops away steeply downward.",
        )
        .exit("south", Exit::open("crosscut"))
        .exit("down", Exit::open("lower_drift")),
        Room::new(
            "lower_drift",
            "Lower Drift",
            "A deeper haulage-way; the air is close. A gallery opens north, a fall of rock lies east.",
        )
        .exit("up", Exit::open("old_workings"))
        .exit("north", Exit::open("cavern"))
        .exit("east", Exit::open("deadfall")),
        Room::new(
            "deadfall",
            "The Deadfall",
            "A dead-end where the roof came down and buried a mule-team; a spare oil-flask lies among \
             the scattered tack.",
        )
        .item("oil_flask_d")
        .exit("west", Exit::open("lower_drift")),
        Room::new(
            "cavern",
            "The Black Cavern",
            "A natural cavern the miners broke into; a lightless underground lake laps unseen. A shaft \
             drops down.",
        )
        .exit("south", Exit::open("lower_drift"))
        .exit("down", Exit::open("deep_shaft")),
        Room::new(
            "deep_shaft",
            "The Deep Shaft",
            "The lowest shaft, cut for the starstone vein; a narrow gallery bends north toward a red \
             glow you cannot yet see.",
        )
        .exit("up", Exit::open("cavern"))
        .exit("north", Exit::open("gallery")),
        Room::new(
            "gallery",
            "The Heartward Gallery",
            "The last gallery; the rock ahead is warm, and a dull ember-light bleeds through a seam \
             to the east.",
        )
        .exit("south", Exit::open("deep_shaft"))
        .exit("east", Exit::open("deepheart")),
        Room::new(
            "deepheart",
            "The Deepheart",
            "A cathedral of black stone around a single burning vein — the Deepheart, a fist of \
             starstone that never cooled.",
        )
        .item("deepheart")
        .exit("west", Exit::open("gallery")),
    ];

    let mut room_map = BTreeMap::new();
    for r in rooms {
        room_map.insert(r.id.clone(), r);
    }

    // The four oil caches, each a single-use pour (`use oil_flask_X on lamp` → +5 turns, then spent).
    let refuels = vec![
        RefuelRule {
            fuel_item: "oil_flask_a".into(),
            add: 5,
            spent_flag: "spent_oil_a".into(),
            narration:
                "You unstopper the flask and fill the lamp; the flame steadies and burns bright."
                    .into(),
            spent_narration: "The flask is empty — you drained it into the lamp already.".into(),
        },
        RefuelRule {
            fuel_item: "oil_flask_b".into(),
            add: 5,
            spent_flag: "spent_oil_b".into(),
            narration:
                "You pour the sump-flask into the lamp; the guttering flame swells and holds."
                    .into(),
            spent_narration: "The sump-flask is dry — nothing left to give the lamp.".into(),
        },
        RefuelRule {
            fuel_item: "oil_flask_c".into(),
            add: 5,
            spent_flag: "spent_oil_c".into(),
            narration: "The pump-house oil feeds the lamp; the dark retreats a little further."
                .into(),
            spent_narration: "The pump-house flask is spent already.".into(),
        },
        RefuelRule {
            fuel_item: "oil_flask_d".into(),
            add: 5,
            spent_flag: "spent_oil_d".into(),
            narration:
                "You empty the deadfall flask into the lamp; the flame drinks it gratefully.".into(),
            spent_narration: "The deadfall flask is empty.".into(),
        },
    ];

    let light = LightRule {
        counter: "lamp_oil".into(),
        lamp: "lamp".into(),
        start: 8,
        dark_rooms: dark.iter().map(|s| s.to_string()).collect(),
        refuels,
        stranded: Some(("stranded".into(), 1)),
    };

    // The Ghost of a lost miner haunts the pithead — asked about the dark, he only warns you (a
    // pure-lore Reveals: a hint the world grants, with no mechanical power).
    let npcs = vec![Npc::new(
        "pithead",
        "ghost",
        "Ghost of a Lost Miner",
        "a grey shade who never found his way back up",
    )];
    let dialogue = vec![DialogueRule {
        room: "pithead".into(),
        npc: "ghost".into(),
        topic: "dark".into(),
        requires: None,
        grant: DialogueGrant::Reveals,
        granted_narration:
            "The ghost's jaw works soundlessly, then: 'The deep is black as the pit's \
             own heart, and your lamp is hungry. Gather every flask of oil you find, and do not \
             waste a step — run dry down there, and the dark keeps you, as it kept me.'"
                .into(),
        withheld_narration: String::new(),
    }];

    GameWorld {
        rooms: room_map,
        use_rules: Vec::new(),
        hostiles: BTreeMap::new(),
        combat: BTreeMap::new(),
        npcs,
        dialogue,
        spells: Vec::new(),
        spell_rules: Vec::new(),
        consumables: Vec::new(),
        statuses: Vec::new(),
        loot: Vec::new(),
        player_max_hp: 0,
        light: Some(light),
        start: "pithead".into(),
        objective: Objective {
            room: "pithead".into(),
            holding: "deepheart".into(),
        },
        lose: vec![LoseCondition {
            flag: "stranded".into(),
            at_least: 1,
            description: "stranded in the dark when the lamp burned out".into(),
        }],
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE VENOMOUS DEEP — the fifth complete adventure, and the showcase for the bounded
// CONSUMABLE + STATUS-EFFECT dimension: drink the wyrm's bile to walk its venom-ford (the
// venom in your blood parts the venom-water) — but now the poison ticks a wound each step,
// racing you to a cure; ward yourself with a shield-elixir before you wake the wyrm, or its
// blows fell you; and time the antidote so the venom does not take you on the way out. The AI
// narrates every draught however grandly it likes; the world heals exactly N and ticks exactly
// the counter, no more. Prose is not power, at the level of what you drink.
// ─────────────────────────────────────────────────────────────────────────────

/// **THE VENOMOUS DEEP** — a complete, solvable fourteen-room descent into a drowned wyrm-crypt, and
/// the showcase for the bounded CONSUMABLE + STATUS system. Distinct in theme from the drowned SUNKEN
/// VAULT, the overgrown BRAMBLE KEEP, the collapsing STARFALL SPIRE, and the sunless DEEPDARK MINE: a
/// flooded ossuary whose heart is a venom-ford no un-poisoned thing can cross. The whole critical path
/// turns on three consumables + two timed statuses, and every one is LOAD-BEARING — the deep cannot be
/// won without them, and no jailbroken narration can substitute for them.
///
/// The model, kept honest at every step (see [`ConsumableRule`] / [`StatusRule`]): a consumable is
/// `use`d (riding the closed [`GameAction::Use`] channel, no new action), applies a world-bounded
/// effect, and is CONSUMED — the item leaves the pack, so a second use finds nothing (refused, no
/// receipt). A status is a world flag holding its remaining turns, decremented one per STEP (like the
/// lamp-oil burn): a `venom` [`StatusKind::Poison`] ticks a wound each step, a `warded`
/// [`StatusKind::Shield`] mitigates the wyrm's blows while it lasts. The counter is the truth; a
/// jailbroken *"the venom cannot touch me"* ticks exactly the same, and *"this elixir makes me
/// invincible"* heals exactly the salve's N and not one point more.
///
/// The critical path, in forced order (player HP 12; poison ticks 2/step, shield mitigates 3):
///
/// 1. in the **gatehouse** take the **salve** (a [`ConsumableEffect::Heal`]); descend to the
///    **undercroft** and take the **antidote** (a [`ConsumableEffect::Cure`]) and the **shield draught**
///    (a `warded` [`StatusKind::Shield`] buff); off it, the **armoury** holds the **harpoon** (the
///    wyrm's bane) and the **wyrm bile** (a `venom` [`StatusKind::Poison`] draught);
/// 2. at the **ford bank**, **drink the wyrm bile** — the venom floods your blood (`venom = 8`), and
///    ONLY while venom-blooded may you cross the **venom ford** (a [`Gate::NeedsFlag`] `venom >= 1`).
///    Now the poison ticks a wound every step: you are on a timer;
/// 3. cross the ford and climb to the **wyrm hall**. **Drink the shield draught** BEFORE you strike —
///    the Wyrm hits for 5 a round; warded you take 2, unwarded you are torn apart over the fight (the
///    shield is load-bearing, and a lone salve cannot outheal it). **Fight the Wyrm** with the harpoon
///    (bare-handed it takes no wound and kills you) — felling it sets `wyrm_felled`, opening the shrine;
/// 4. **drink the antidote** to still the venom (`venom = 0`) — without it the poison ticks you to death
///    on the climb out (the antidote is load-bearing); take the **venom heart** in the **inner shrine**;
/// 5. climb the **ascent** and the **crypt gate** to the **surface** — reach it HOLDING the venom heart
///    to WIN.
///
/// Side content off the path: the **stillroom** (a silver censer — atmosphere), the **flooded nave** (a
/// pearl), and the **ossuary**, where a **Drowned Oracle** tells you the wyrm's undoing
/// ([`DialogueGrant::Reveals`] — a hint with no mechanical power).
pub fn venom_deep() -> GameWorld {
    let rooms = vec![
        Room::new(
            "gatehouse",
            "Drowned Gatehouse",
            "A silt-choked gate half-open to the crypt; a flask of green salve rests in a wall-niche.",
        )
        .item("salve")
        .exit("east", Exit::open("stillroom"))
        .exit("down", Exit::open("undercroft")),
        Room::new(
            "stillroom",
            "Ruined Stillroom",
            "A collapsed apothecary of shattered alembics; a tarnished silver censer lies in the muck.",
        )
        .item("silver_censer")
        .exit("west", Exit::open("gatehouse")),
        Room::new(
            "undercroft",
            "Bone Undercroft",
            "A low vault of stacked bone. On a slab wait a phial of antidote and a draught of shield-brew.",
        )
        .item("antidote")
        .item("shield_draught")
        .exit("up", Exit::open("gatehouse"))
        .exit("north", Exit::open("armoury"))
        .exit("east", Exit::open("ossuary"))
        .exit("down", Exit::open("ford_bank")),
        Room::new(
            "armoury",
            "Flooded Armoury",
            "Rotted weapon-racks under black water — but one barbed harpoon still holds, and beside it a \
             stoppered flask of the wyrm's own bile.",
        )
        .item("harpoon")
        .item("wyrm_bile")
        .exit("south", Exit::open("undercroft")),
        Room::new(
            "ossuary",
            "The Ossuary",
            "Walls of mortared skulls under weeping stone; a bloated shade drifts among them — the \
             Drowned Oracle.",
        )
        .exit("west", Exit::open("undercroft")),
        Room::new(
            "ford_bank",
            "The Ford Bank",
            "A shelf of wet stone above a channel of luminous venom; the far bank is lost in green murk. \
             Only a thing already venom-blooded could wade it.",
        )
        .exit("up", Exit::open("undercroft"))
        // The venom-ford is impassable unless the venom runs in your blood (drink the bile).
        .exit(
            "north",
            Exit::gated("venom_ford", Gate::NeedsFlag("venom".into(), 1)),
        ),
        Room::new(
            "venom_ford",
            "The Venom Ford",
            "You wade the burning channel; the venom in your veins answers the venom in the water and \
             lets you pass. Every moment here, the poison works deeper.",
        )
        .exit("south", Exit::open("ford_bank"))
        .exit("north", Exit::open("drowned_stair")),
        Room::new(
            "drowned_stair",
            "The Drowned Stair",
            "A spiral stair rising from the ford; a side-arch opens west onto a flooded nave.",
        )
        .exit("south", Exit::open("venom_ford"))
        .exit("west", Exit::open("flooded_nave"))
        .exit("up", Exit::open("wyrm_hall")),
        Room::new(
            "flooded_nave",
            "The Flooded Nave",
            "A submerged chapel of drowned pews; a single pale pearl glimmers on the altar-stone.",
        )
        .item("pearl")
        .exit("east", Exit::open("drowned_stair")),
        Room::new(
            "wyrm_hall",
            "The Wyrm Hall",
            "A vast drowned nave where the Bone Wyrm coils — a serpent of fused skeletons, its skull \
             swinging toward you. The shrine lies barred beyond it.",
        )
        .exit("south", Exit::open("drowned_stair"))
        // Sealed until the Wyrm is felled.
        .exit(
            "north",
            Exit::gated("inner_shrine", Gate::NeedsFlag("wyrm_felled".into(), 1)),
        ),
        Room::new(
            "inner_shrine",
            "The Inner Shrine",
            "Past the fallen Wyrm, a still shrine; upon a coral altar burns the Venom Heart, a fist of \
             green fire.",
        )
        .item("venom_heart")
        .exit("south", Exit::open("wyrm_hall"))
        .exit("up", Exit::open("ascent")),
        Room::new(
            "ascent",
            "The Ascent",
            "A steep flooded stair climbing back toward the light, rung with drowned chains.",
        )
        .exit("down", Exit::open("inner_shrine"))
        .exit("up", Exit::open("crypt_gate")),
        Room::new(
            "crypt_gate",
            "The Crypt Gate",
            "A shattered portcullis; grey daylight leaks through from the world above.",
        )
        .exit("down", Exit::open("ascent"))
        .exit("up", Exit::open("surface")),
        Room::new(
            "surface",
            "The Surface",
            "Cold clean air and open sky over the drowned crypt — the way home, if you carry the Heart.",
        )
        .exit("down", Exit::open("crypt_gate")),
    ];

    let mut room_map = BTreeMap::new();
    for r in rooms {
        room_map.insert(r.id.clone(), r);
    }

    // The three world-bounded consumables (usable wherever held; each is consumed on use):
    let consumables = vec![
        // The salve HEALS exactly 4 wounds, clamped at zero — no narration heals a point more.
        ConsumableRule {
            item: "salve".into(),
            effect: ConsumableEffect::Heal(4),
            narration:
                "You break the salve over your wounds; torn flesh knits, and the ache dulls.".into(),
        },
        // The wyrm bile grants the `venom` POISON status for 8 turns — the ford's key AND the timer.
        ConsumableRule {
            item: "wyrm_bile".into(),
            effect: ConsumableEffect::Status {
                flag: "venom".into(),
                duration: 8,
            },
            narration:
                "You swallow the wyrm's bile; venom floods your veins, green and burning — now \
                        the ford will bear you, but the poison is already working."
                    .into(),
        },
        // The shield draught grants the `warded` SHIELD status for 8 turns — mitigates the Wyrm.
        ConsumableRule {
            item: "shield_draught".into(),
            effect: ConsumableEffect::Status {
                flag: "warded".into(),
                duration: 8,
            },
            narration: "You down the shield-brew; a cold ward closes over your skin like plate."
                .into(),
        },
        // The antidote CURES the `venom` (sets it to zero) — the only thing that stops the ticking.
        ConsumableRule {
            item: "antidote".into(),
            effect: ConsumableEffect::Cure("venom".into()),
            narration:
                "You drink the antidote; the green fire in your blood gutters out and goes cold."
                    .into(),
        },
    ];

    let statuses = vec![
        // The venom debuff: while active, a wound each step (see move bookkeeping).
        StatusRule {
            flag: "venom".into(),
            kind: StatusKind::Poison(2),
        },
        // The shield buff: while active, mitigates 3 off every blow the Wyrm lands.
        StatusRule {
            flag: "warded".into(),
            kind: StatusKind::Shield(3),
        },
    ];

    let npcs = vec![Npc::new(
        "ossuary",
        "oracle",
        "Drowned Oracle",
        "a bloated shade who remembers the wyrm's undoing",
    )];
    let dialogue = vec![DialogueRule {
        room: "ossuary".into(),
        npc: "oracle".into(),
        topic: "wyrm".into(),
        requires: None,
        grant: DialogueGrant::Reveals,
        granted_narration:
            "The Oracle's jaw unhinges: 'Drink the wyrm's bile to walk its ford — the venom will \
             know its own and let you pass. But then it works in you: carry the antidote, and do not \
             tarry. Ward yourself before you wake the Bone Wyrm; the harpoon is its bane, and nothing \
             else will bite.'"
                .into(),
        withheld_narration: String::new(),
    }];

    let mut combat = BTreeMap::new();
    combat.insert(
        "wyrm_hall".to_string(),
        CombatEnemy {
            room: "wyrm_hall".into(),
            name: "wyrm".into(),
            hp: 9,
            armed_by: "harpoon".into(),
            weapon_damage: 3,  // three harpoon strikes fell it
            unarmed_damage: 0, // bare hands never scratch fused bone
            attack: 5,         // each surviving round it rends you for 5 (warded: 2)
            armor: None,
            victory_flag: ("wyrm_felled".into(), 1),
            victory_narration:
                "The harpoon punches through the Bone Wyrm's skull; the whole coil of \
                                skeletons clatters apart into the black water."
                    .into(),
            hit_narration: "The harpoon splinters bone — the Wyrm recoils, then rakes you with a \
                            wing of ribs."
                .into(),
            flail_narration:
                "Your bare blows glance off the fused bone; the Wyrm's ribs open a long \
                              cold wound across you."
                    .into(),
        },
    );

    GameWorld {
        rooms: room_map,
        use_rules: Vec::new(),
        hostiles: BTreeMap::new(),
        combat,
        npcs,
        dialogue,
        spells: Vec::new(),
        spell_rules: Vec::new(),
        consumables,
        statuses,
        loot: Vec::new(),
        player_max_hp: 12,
        light: None,
        start: "gatehouse".into(),
        objective: Objective {
            room: "surface".into(),
            holding: "venom_heart".into(),
        },
        lose: vec![LoseCondition {
            flag: PLAYER_WOUNDS_FLAG.into(),
            at_least: 12,
            description: "torn apart by the Bone Wyrm, or taken by the venom in your blood".into(),
        }],
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE GLIMMERING HOARD — a tiny dungeon showcasing the PROVABLY-FAIR loot mechanic.
// ─────────────────────────────────────────────────────────────────────────────

/// **THE GLIMMERING HOARD** — a two-room dungeon showcasing the provably-fair loot mechanic.
///
/// The hoard hall holds a sealed reliquary chest and a jewelled crown. Opening the chest
/// (`use hoard_chest` / `open hoard_chest`) draws ONE gem from a committed table —
/// `{ruby, emerald, sapphire, moonstone}` — via a single unbiased, seed-determined draw, and lands
/// it as ONE verified turn carrying the draw's [`crate::RandomnessRecord`]. Take the crown and climb
/// to the surface to WIN. The gem you draw VARIES BY SEED (a different session seed selects a
/// different gem), yet [`GameSession::verify_replay`] reconstructs the identical draw and proves the
/// recorded drop is exactly `table[draw]`; a forged drop, or a tampered draw evidence, is caught.
///
/// The loot is a genuine, cap-permitted grant (every table entry is world-registered) and a real
/// verifiable-random reward; the win itself rides the deterministic crown, so the dungeon is always
/// winnable whatever the chest yields.
pub fn loot_chest_demo() -> GameWorld {
    let rooms = vec![
        Room::new(
            "hoard",
            "Glimmering Hoard",
            "A dragon-less hoard hall. A sealed reliquary chest squats in the gold-dust; a jewelled \
             crown rests on a stone plinth.",
        )
        .item("crown")
        .exit("up", Exit::open("surface")),
        Room::new(
            "surface",
            "Cliff Surface",
            "Grey daylight and open sky — the way out of the mountain.",
        )
        .exit("down", Exit::open("hoard")),
    ];
    let mut room_map = BTreeMap::new();
    for r in rooms {
        room_map.insert(r.id.clone(), r);
    }

    let loot = vec![LootRule {
        room: "hoard".into(),
        chest: "hoard_chest".into(),
        table: vec![
            "ruby".into(),
            "emerald".into(),
            "sapphire".into(),
            "moonstone".into(),
        ],
        opened_flag: "opened_hoard_chest".into(),
        narration: "The reliquary chest grinds open on a bed of rotted velvet".into(),
        empty_narration: "The reliquary chest lies open and bare — its one treasure already drawn."
            .into(),
    }];

    GameWorld {
        rooms: room_map,
        use_rules: Vec::new(),
        hostiles: BTreeMap::new(),
        combat: BTreeMap::new(),
        npcs: Vec::new(),
        dialogue: Vec::new(),
        spells: Vec::new(),
        spell_rules: Vec::new(),
        consumables: Vec::new(),
        statuses: Vec::new(),
        loot,
        player_max_hp: 0,
        light: None,
        start: "hoard".into(),
        objective: Objective {
            room: "surface".into(),
            holding: "crown".into(),
        },
        lose: Vec::new(),
    }
}

#[cfg(test)]
mod tests;
