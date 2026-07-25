//! # The `.dungeon` → deployed-substrate COMPILER, with translation validation.
//!
//! [`compile_world`] lowers a parsed [`GameWorld`] onto the REAL executor: it builds a
//! [`spween::Scene`] whose passages/choices mirror the room graph, hands it to the
//! spween-dregg v0 compiler ([`compile_scene`] — the UNTRUSTED lowering), AUGMENTS the
//! program with staple-closure teeth, and then CHECKS the output against the source
//! ruleset before returning it ([`check_lowering`] — the trusted validator). A
//! [`CompiledDungeon`] that fails the check is a [`CompileError::ValidationFailed`]
//! naming the mismatch, never a success. Deploy with [`CompiledDungeon::deploy`]: the
//! same [`WorldCell::deploy_compiled`] path the hand-written worlds use, so every gate
//! is a real `CellProgram` tooth the verified executor re-checks per turn.
//!
//! ## The lowering table (source construct → real executor artifact)
//!
//! | `.dungeon` construct              | lowered to                                                    |
//! |-----------------------------------|---------------------------------------------------------------|
//! | room + description                | one scene passage (prose)                                     |
//! | item placed in a room             | a `Take` choice: `~ has_<item> = 1`, self-target              |
//! | `exit <dir> -> <room>`            | a `Go` choice navigating to the target passage                |
//! | `exit … requires item <i>`        | choice condition `{ has_<i> >= 1 }` → executor `FieldGte`     |
//! | `exit … requires flag <f> >= v`   | choice condition `{ flag_<f> >= v }` → executor `FieldGte`    |
//! | `use <i> [on <t>] in <r> -> flag` | a gated choice: `{ has_<i> >= 1 } ~ flag_<f> = v`             |
//! | `npc topic … -> gives <i>`        | a gated choice: `{ <requires> } ~ has_<i> = 1`                |
//! | `npc topic … -> opens <f>`        | a gated choice: `{ <requires> } ~ flag_<f> = v`               |
//! | `npc topic … -> reveals`          | an ungated pure-narration choice (no effects)                 |
//! | `objective: reach <r> holding <i>`| a `Claim` choice in `<r>`: `{ has_<i> >= 1 } ~ dungeon_won = 1 -> END` |
//! | `requires A and B`                | the CONJUNCTION of both gates' teeth on that one case         |
//! | `requires flag <f> is <v>`        | choice condition `{ flag_<f> == v }` → executor `FieldEquals` |
//! | `topic … once` / `use … once`     | `{ once_<tag> <= 0 } ~ once_<tag> += 1` → executor `FieldLte` |
//! | `oath <o>` branch `<b>`           | `{ flag_sworn_<o> <= 0 } ~ flag_sworn_<o> += 1, flag_oath_<o>_<b> = 1` |
//!
//! ## Exclusion is a real tooth, not a convention
//!
//! Three of those rows exist to make a dungeon capable of saying NO. Everything else in
//! the grammar is monotone — a flag rises, an item is held, and nothing ever closes — so
//! before them an authored dungeon could only be a checklist: no oath, no betrayal, no
//! burned bridge, no revelation you get once. The mechanism is one primitive used three
//! ways: a SPEND COUNTER the choice both gates on (`<= 0`, pre-state) and bumps (`+= 1`),
//! which the v0 compiler lifts to a post-state `FieldLte { value: 1 }`. A second attempt
//! has a pre-state of `1`, a post-state of `2`, and is a real
//! [`WorldError`](spween_dregg::WorldError)`::Refused` that commits nothing. An `oath`
//! shares ONE counter across its branches, so swearing any branch forecloses the rest.
//!
//! Note the shape this forces: the gated var must be bumped by a `+=`, never assigned.
//! The v0 compiler treats a `Set` on a var the same choice gates as un-lowerable
//! (`Delta::Overwritten`) and clears `fully_gated`, which [`check_lowering`] then refuses
//! — so a spend counter written with `=` fails the build rather than deploying ungated.
//!
//! ## Substrate posture, said out loud
//!
//! These constructs introduce NO new constraint kind and no new admitted verb. They
//! compose `FieldGte` / `FieldLte` / `FieldEquals` / `Immutable` / `HeapField{Gte,Lte,
//! Equals,Immutable}` — all inside the subset that `Dregg2.Exec.DeployedConstraint`
//! decides and that a deployed node routes through the verified
//! `dregg_constraint_admits` oracle. What is Rust here is the LOWERING FUNCTION
//! ([`choice_spec`] and [`augment`]), and that is the honest debt: the Descent's teeth are
//! a Lean-authored value emitted to `dungeon-on-dregg/program/dungeon_program.json`,
//! whereas an authored world's teeth are computed by this file. See the module footer.
//!
//! Item possession / flag state are cell registers allocated by the v0 compiler
//! (spilling to the committed ext plane past the 15th var, same as every compiled
//! scene). Beyond what the v0 compiler emits, [`compile_world`] AUGMENTS each case
//! with two staple-closure teeth (the `keep_compiled` idiom from the crate root):
//!
//! * **a nav pin** — `FieldEquals(PASSAGE_SLOT, <the choice's declared target>)`, so a
//!   `SetField(PASSAGE_SLOT, elsewhere)` stapled onto a legit choice method (via
//!   [`WorldCell::apply_raw`]) cannot teleport;
//! * **write confinement** — `Immutable` (register) / `HeapField{Immutable}` (ext) for
//!   every state var the choice does NOT legitimately write, on every case (genesis
//!   included), so an item/flag grant stapled onto another method's turn is a real
//!   executor refusal. The one-shot genesis sentinel and the heap-hatch register
//!   freeze come from the v0 compiler unchanged.
//!
//! ## Translation validation (the non-negotiable)
//!
//! [`check_lowering`] re-derives, FROM THE SOURCE RULESET, the exact constraint
//! multiset every case must carry — each gate the validator says guards an
//! exit/topic/use/objective becomes an expected `FieldGte` tooth (resolved by NAME
//! through the compiled layout, never a guessed index) — and compares it against the
//! INSTALLED program, both directions:
//!
//! * **no missing teeth** — a source gate with no corresponding executor constraint is
//!   a named `ValidationFailed` (and every gated choice must be `fully_gated`: no
//!   handler-only clause is accepted);
//! * **no phantom teeth** — a program constraint no source construct (or documented
//!   augmentation) accounts for is a named `ValidationFailed`, as is an unrecognized
//!   case or a non-`MethodIs` guard.
//!
//! ## Honest residuals — what this compiler does NOT lower (fail-closed, named)
//!
//! A world using any of these is refused with [`CompileError::Unsupported`] naming the
//! construct (never a silent drop): `hostile` (one-shot foes), `combat` (HP fights),
//! `spell` / spell rules, `consumable`, `status`, `light` (the oil budget), `lose:`
//! conditions (nothing lowers a lose-flag terminal yet), and `player_hp:`. Each has a
//! proven executor idiom in this crate (`combat`, `spells`, `meta`, …) — wiring the
//! compiler to them is the scheduled sharpening, and the named error is the tooth that
//! keeps the residual honest until then.
//!
//! Also deliberately NOT routed through `dregg-schema`: its emitter
//! (`dregg_schema::emit::emit_program`) lowers a whole schema onto ONE `move`-guarded
//! case, while a dungeon needs per-choice dispatch (a gate guards ONE move, not every
//! move). The archetype route fits a stat-sheet game, not a room graph; state here is
//! laid out by the same v0 compiler every deployed scene uses, and the layout is
//! checked by this module's own translation validation instead.
//!
//! Two substrate postures shared with every compiled scene (not introduced here): a
//! choice's case does not verify the CURRENT passage (a client presenting another
//! room's choice method moves the passage slot to that choice's declared target —
//! caught by `verify_by_replay`'s passage-order check on the record, and the nav pin
//! keeps even that landing on the declared target); and register teeth are
//! executor-enforced, in-circuit-projected only for register-plane constraints.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use dregg_app_framework::{CellProgram, StateConstraint, TransitionGuard, field_from_u64, symbol};
use dregg_cell::program::HeapAtom;
use spween::{
    Choice, CompareClause, CompareOp, Condition, ConditionClause, ConditionExpr, Effect,
    ModifyEffect, NavigationTarget, Passage, PassageContent, Prose, Scene, SceneMeta, SetEffect,
    Value,
};
use spween_dregg::{
    CompiledStory, GENESIS_DONE_EXT_KEY, GENESIS_METHOD, HEAP_HATCH_METHOD, PASSAGE_ENDED,
    PASSAGE_SLOT, STATE_SLOTS, WorldCell, WorldError, choice_method, compile_scene,
};

use super::ir::{DialogueGrant, GameWorld, Gate, OathRule};
use super::validate::validate;

/// The compiled var holding "the objective was claimed" (`1` after the win choice).
pub const DUNGEON_WON_VAR: &str = "dungeon_won";

/// The compiled var holding possession of `item` (`1` once taken/granted).
pub fn item_var(item: &str) -> String {
    format!("has_{item}")
}

/// The compiled var carrying world flag `flag`.
pub fn flag_var(flag: &str) -> String {
    format!("flag_{flag}")
}

/// The compiled SPEND COUNTER for a `once` construct tagged `tag` — `0` while unspent,
/// bumped to `1` by the turn that fires it. Its own namespace, so it can never collide
/// with an author's flag (`flag_…`) or item (`has_…`).
pub fn once_var(tag: &str) -> String {
    format!("once_{tag}")
}

/// The `once` tag of the dialogue rule at `dialogue_index`.
fn talk_once_tag(world: &GameWorld, dialogue_index: usize) -> String {
    let d = &world.dialogue[dialogue_index];
    format!("talk_{}_{}", d.npc, d.topic)
}

/// The `once` tag of the use-rule at `use_index`. Positional: a use-rule's identity in
/// the source IS its position, and two rules that agreed on room+item+target would
/// otherwise silently SHARE a counter (either one firing closing both).
fn use_once_tag(use_index: usize) -> String {
    format!("use_{use_index}")
}

// ─────────────────────────────────────────────────────────────────────────────
// Errors.
// ─────────────────────────────────────────────────────────────────────────────

/// Why a [`GameWorld`] could not be compiled to a deployable dungeon.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CompileError {
    /// The world fails its own validator with blocking errors — compile refuses
    /// before lowering (a broken dungeon never becomes a cell program).
    WorldInvalid {
        /// The first blocking validator message.
        first: String,
        /// How many blocking errors the validator reported.
        errors: usize,
    },
    /// The world uses a construct this compiler does not lower yet — refused BY NAME,
    /// never silently dropped. See the module header's residual list.
    Unsupported {
        /// The construct, named (e.g. ``hostile `gargoyle` ``).
        construct: String,
    },
    /// The spween-dregg v0 compiler refused the generated scene.
    Scene(spween_dregg::CompileError),
    /// **The translation-validation tooth.** The lowered program does not match the
    /// source ruleset — a missing gate tooth, a phantom constraint, an unrecognized
    /// case. The mismatch is named; the artifact is never returned as a success.
    ValidationFailed {
        /// What mismatched, precisely.
        mismatch: String,
    },
}

impl std::fmt::Display for CompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CompileError::WorldInvalid { first, errors } => {
                write!(
                    f,
                    "world fails validation ({errors} error(s); first: {first})"
                )
            }
            CompileError::Unsupported { construct } => {
                write!(f, "unsupported construct: {construct}")
            }
            CompileError::Scene(e) => write!(f, "scene compile: {e}"),
            CompileError::ValidationFailed { mismatch } => {
                write!(f, "translation validation failed: {mismatch}")
            }
        }
    }
}

impl std::error::Error for CompileError {}

// ─────────────────────────────────────────────────────────────────────────────
// The compiled artifact + its mapping tables.
// ─────────────────────────────────────────────────────────────────────────────

/// What one lowered choice IS in the source ruleset — the room→moves mapping table a
/// driver (or the forge front-end) navigates by.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ChoiceKind {
    /// Take `item` from the room (`~ has_<item> = 1`, self-target).
    Take {
        /// The item taken.
        item: String,
    },
    /// Fire use-rule `use_index` (`world.use_rules[use_index]`).
    UseItem {
        /// Index into [`GameWorld::use_rules`].
        use_index: usize,
    },
    /// Speak dialogue rule `dialogue_index` (`world.dialogue[dialogue_index]`).
    Talk {
        /// Index into [`GameWorld::dialogue`].
        dialogue_index: usize,
    },
    /// Swear one branch of an oath — the irreversible fork. Spends the oath's shared
    /// counter, so every sibling branch is foreclosed by an executor tooth.
    Swear {
        /// Index into [`GameWorld::oaths`].
        oath_index: usize,
        /// Index into that oath's [`OathRule::branches`](super::ir::OathRule::branches).
        branch_index: usize,
    },
    /// Walk the exit `dir` (to `world.rooms[room].exits[dir]`).
    Exit {
        /// The exit direction.
        dir: String,
    },
    /// Claim the objective (only in the objective room; `-> END`).
    Objective,
}

/// One lowered choice: where it lives, the dispatch method its turn presents, and
/// what it is in the source ruleset.
#[derive(Clone, Debug)]
pub struct LoweredChoice {
    /// The room (= passage) the choice belongs to.
    pub room: String,
    /// The choice's index within its passage (what [`WorldCell::apply_choice`] takes).
    pub index: usize,
    /// The dispatch method (`choice_method(room, index)`) — the key of its gate case.
    pub method: String,
    /// The source construct this choice lowers.
    pub kind: ChoiceKind,
}

/// **A compiled, translation-validated dungeon** — everything the deploy path needs:
/// the generated scene (the driver walks it), the compiled+augmented story (the
/// installed `CellProgram` teeth), and the room/choice mapping tables.
#[derive(Clone, Debug)]
pub struct CompiledDungeon {
    /// The generated spween scene (passages mirror rooms; drives choices/prose).
    pub scene: Scene,
    /// The compiled story: slot layout + the augmented, validated [`CellProgram`].
    pub story: CompiledStory,
    /// Room id → passage index (identical to `story.passage_index`).
    pub rooms: BTreeMap<String, usize>,
    /// Every lowered choice, in (room, index) order — the mapping table.
    pub choices: Vec<LoweredChoice>,
}

impl CompiledDungeon {
    /// **Deploy on the real substrate** — the same
    /// [`WorldCell::deploy_compiled`] path the hand-written worlds use. Deterministic
    /// in `seed` (a re-deploy reproduces the same cell identity + state hashes).
    pub fn deploy(&self, seed: u8) -> Result<WorldCell, WorldError> {
        WorldCell::deploy_compiled(Arc::new(self.story.clone()), seed)
    }

    /// The scene [`Choice`] at (`room`, `index`) — the value
    /// [`WorldCell::apply_choice`] drives directly at the executor.
    pub fn choice(&self, room: &str, index: usize) -> Option<Choice> {
        let passage = self
            .scene
            .passages
            .iter()
            .find(|p| p.name.as_str() == room)?;
        passage
            .content
            .iter()
            .filter_map(|c| match c {
                PassageContent::Choice(ch) => Some(ch),
                _ => None,
            })
            .nth(index)
            .cloned()
    }

    fn find_index(&self, room: &str, pred: impl Fn(&ChoiceKind) -> bool) -> Option<usize> {
        self.choices
            .iter()
            .find(|c| c.room == room && pred(&c.kind))
            .map(|c| c.index)
    }

    /// The choice index of taking `item` in `room`.
    pub fn take_index(&self, room: &str, item: &str) -> Option<usize> {
        self.find_index(
            room,
            |k| matches!(k, ChoiceKind::Take { item: i } if i == item),
        )
    }

    /// The choice index of walking exit `dir` out of `room`.
    pub fn exit_index(&self, room: &str, dir: &str) -> Option<usize> {
        self.find_index(
            room,
            |k| matches!(k, ChoiceKind::Exit { dir: d } if d == dir),
        )
    }

    /// The choice index of dialogue rule `dialogue_index` (in its own room).
    pub fn talk_index(&self, room: &str, dialogue_index: usize) -> Option<usize> {
        self.find_index(
            room,
            |k| matches!(k, ChoiceKind::Talk { dialogue_index: d } if *d == dialogue_index),
        )
    }

    /// The choice index of the objective claim (in the objective room).
    pub fn objective_index(&self, room: &str) -> Option<usize> {
        self.find_index(room, |k| matches!(k, ChoiceKind::Objective))
    }

    /// The choice index of swearing branch `branch` of oath `oath` (in the oath's room).
    pub fn swear_index(&self, room: &str, oath: usize, branch: usize) -> Option<usize> {
        self.find_index(room, |k| {
            matches!(
                k,
                ChoiceKind::Swear { oath_index, branch_index }
                    if *oath_index == oath && *branch_index == branch
            )
        })
    }

    /// The executor-enforced constraints installed on the case guarded by (`room`,
    /// `index`)'s method — introspection proof the gate is a real kernel predicate.
    pub fn gate_constraints(&self, room: &str, index: usize) -> Vec<StateConstraint> {
        let m = symbol(&choice_method(room, index));
        let CellProgram::Cases(cases) = &self.story.program else {
            return Vec::new();
        };
        cases
            .iter()
            .find(|c| matches!(&c.guard, TransitionGuard::MethodIs { method } if *method == m))
            .map(|c| c.constraints.clone())
            .unwrap_or_default()
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The choice enumeration — ONE deterministic order, shared by the scene builder
// and the translation validator.
// ─────────────────────────────────────────────────────────────────────────────

/// The per-room choice enumeration, in the canonical order: takes (item-sorted), then
/// use-rules (declaration order), then dialogue (declaration order), then exits
/// (direction-sorted), then — in the objective room — the claim.
fn room_choice_kinds(world: &GameWorld, room_id: &str) -> Vec<ChoiceKind> {
    let mut kinds = Vec::new();
    let room = &world.rooms[room_id];
    for item in &room.items {
        kinds.push(ChoiceKind::Take { item: item.clone() });
    }
    for (i, u) in world.use_rules.iter().enumerate() {
        if u.room == room_id {
            kinds.push(ChoiceKind::UseItem { use_index: i });
        }
    }
    for (i, d) in world.dialogue.iter().enumerate() {
        if d.room == room_id {
            kinds.push(ChoiceKind::Talk { dialogue_index: i });
        }
    }
    for (oi, o) in world.oaths.iter().enumerate() {
        if o.room == room_id {
            for bi in 0..o.branches.len() {
                kinds.push(ChoiceKind::Swear {
                    oath_index: oi,
                    branch_index: bi,
                });
            }
        }
    }
    for dir in room.exits.keys() {
        kinds.push(ChoiceKind::Exit { dir: dir.clone() });
    }
    if world.objective.room == room_id {
        kinds.push(ChoiceKind::Objective);
    }
    kinds
}

/// The room (= passage) order: the start room first (passage 0 is where a fresh cell
/// opens), then the rest sorted by id.
fn room_order(world: &GameWorld) -> Vec<String> {
    let mut order = vec![world.start.clone()];
    order.extend(world.rooms.keys().filter(|r| **r != world.start).cloned());
    order
}

/// The comparison one gate term makes against the PRE-state of its var. Each maps to
/// exactly one `spween` [`CompareOp`], hence to exactly one executor tooth.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum GateOp {
    /// `var >= base` — the ordinary "you have it" gate.
    Gte,
    /// `var == base` — the EXCLUSIVE gate (`requires flag oath is 2`).
    Eq,
    /// `var <= base` — the SPEND gate (`once` / an oath's counter).
    Lte,
}

impl GateOp {
    fn compare_op(self) -> CompareOp {
        match self {
            GateOp::Gte => CompareOp::Ge,
            GateOp::Eq => CompareOp::Eq,
            GateOp::Lte => CompareOp::Le,
        }
    }
}

/// One term of a choice's gate: `var <op> base`, over the PRE-state.
#[derive(Clone, Debug)]
struct GateTerm {
    var: String,
    op: GateOp,
    base: i64,
}

/// How one of a choice's effects writes its var.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum WriteKind {
    /// `~ var = v` — an assignment. Never permitted on a var the SAME choice gates
    /// (the v0 compiler cannot lift a gate over an overwritten var).
    Set(i64),
    /// `~ var += d` — a bump. This is what a spend counter uses, so its own gate stays
    /// liftable.
    Add(i64),
}

/// One lowered write: the compiled var and how it moves.
#[derive(Clone, Debug)]
struct Write {
    var: String,
    kind: WriteKind,
}

impl Write {
    fn set(var: String, v: i64) -> Write {
        Write {
            var,
            kind: WriteKind::Set(v),
        }
    }
    fn add(var: String, d: i64) -> Write {
        Write {
            var,
            kind: WriteKind::Add(d),
        }
    }
}

/// One lowered choice, source-derived: its gate (a CONJUNCTION of terms), the vars its
/// effects legitimately write, and its navigation target.
struct ChoiceSpec {
    #[allow(dead_code)]
    kind: ChoiceKind,
    /// The source gate as a conjunction of terms, in compiled-var terms. Empty = ungated.
    gates: Vec<GateTerm>,
    /// The compiled vars this choice's effects write.
    writes: Vec<Write>,
    /// The navigation target: `Some(room)` or `None` for `-> END`.
    nav: Option<String>,
    /// The display label.
    label: String,
}

impl ChoiceSpec {
    /// The set of vars this choice legitimately writes (what write-confinement spares).
    fn written(&self) -> BTreeSet<&String> {
        self.writes.iter().map(|w| &w.var).collect()
    }

    /// The choice's NET additive delta on `var` — the shift the v0 compiler applies when
    /// it lifts a pre-state comparison to a post-state tooth. A `Set` yields `None`: the
    /// v0 compiler refuses to lift a gate over an overwritten var, so a spec that
    /// produced one would silently deploy ungated. [`check_lowering`] turns that `None`
    /// into a named build failure.
    fn delta_on(&self, var: &str) -> Option<i64> {
        let mut sum = 0;
        for w in &self.writes {
            if w.var == var {
                match w.kind {
                    WriteKind::Set(_) => return None,
                    WriteKind::Add(d) => sum += d,
                }
            }
        }
        Some(sum)
    }
}

/// A source [`Gate`] as a conjunction of compiled-var terms. The one place the source
/// gate vocabulary meets the executor's comparison vocabulary.
fn gate_terms(gate: &Gate) -> Vec<GateTerm> {
    gate.atoms()
        .into_iter()
        .map(|atom| match atom {
            Gate::NeedsItem(item) => GateTerm {
                var: item_var(item),
                op: GateOp::Gte,
                base: 1,
            },
            Gate::NeedsFlag(flag, v) => GateTerm {
                var: flag_var(flag),
                op: GateOp::Gte,
                base: *v,
            },
            Gate::FlagIs(flag, v) => GateTerm {
                var: flag_var(flag),
                op: GateOp::Eq,
                base: *v,
            },
            Gate::All(_) => unreachable!("`Gate::atoms` never yields an `All`"),
        })
        .collect()
}

/// The gate terms of an optional source gate (empty for ungated).
fn opt_gate_terms(gate: &Option<Gate>) -> Vec<GateTerm> {
    gate.as_ref().map(gate_terms).unwrap_or_default()
}

/// The spend-counter pair a `once` construct contributes: gate the counter unspent,
/// then bump it. Used by `once` topics, `once` use-rules, and every oath branch.
fn spend(counter: String) -> (GateTerm, Write) {
    (
        GateTerm {
            var: counter.clone(),
            op: GateOp::Lte,
            base: 0,
        },
        Write::add(counter, 1),
    )
}

/// The full source-derived spec of one choice — THE single place a source construct's
/// gate/writes/nav semantics are defined, used by both the scene builder and
/// [`check_lowering`].
fn choice_spec(world: &GameWorld, room_id: &str, kind: &ChoiceKind) -> ChoiceSpec {
    match kind {
        ChoiceKind::Take { item } => ChoiceSpec {
            kind: kind.clone(),
            gates: vec![],
            writes: vec![Write::set(item_var(item), 1)],
            nav: Some(room_id.to_string()),
            label: format!("Take the {item}"),
        },
        ChoiceKind::UseItem { use_index } => {
            let u = &world.use_rules[*use_index];
            let label = match &u.target {
                Some(t) => format!("Use the {} on the {t}", u.item),
                None => format!("Use the {}", u.item),
            };
            let mut gates = vec![GateTerm {
                var: item_var(&u.item),
                op: GateOp::Gte,
                base: 1,
            }];
            let mut writes = vec![Write::set(flag_var(&u.sets_flag.0), u.sets_flag.1)];
            if u.once {
                let (g, w) = spend(once_var(&use_once_tag(*use_index)));
                gates.push(g);
                writes.push(w);
            }
            ChoiceSpec {
                kind: kind.clone(),
                gates,
                writes,
                nav: Some(room_id.to_string()),
                label,
            }
        }
        ChoiceKind::Talk { dialogue_index } => {
            let d = &world.dialogue[*dialogue_index];
            let mut writes = match &d.grant {
                DialogueGrant::GivesItem(i) => vec![Write::set(item_var(i), 1)],
                DialogueGrant::OpensFlag(k, v) => vec![Write::set(flag_var(k), *v)],
                DialogueGrant::Reveals => vec![],
            };
            let mut gates = opt_gate_terms(&d.requires);
            if d.once {
                let (g, w) = spend(once_var(&talk_once_tag(world, *dialogue_index)));
                gates.push(g);
                writes.push(w);
            }
            ChoiceSpec {
                kind: kind.clone(),
                gates,
                writes,
                nav: Some(room_id.to_string()),
                label: format!("Ask {} about {}", d.npc, d.topic),
            }
        }
        ChoiceKind::Swear {
            oath_index,
            branch_index,
        } => {
            let o = &world.oaths[*oath_index];
            let br = &o.branches[*branch_index];
            // ONE counter shared by every branch: swearing any of them spends it, so the
            // siblings are foreclosed by the same tooth that stops a re-swear.
            let (g, w) = spend(flag_var(&OathRule::sworn_flag(&o.id)));
            ChoiceSpec {
                kind: kind.clone(),
                gates: vec![g],
                writes: vec![
                    w,
                    Write::set(flag_var(&OathRule::branch_flag(&o.id, &br.name)), 1),
                ],
                nav: Some(room_id.to_string()),
                label: format!("Swear the {}: {}", o.id, br.name),
            }
        }
        ChoiceKind::Exit { dir } => {
            let exit = &world.rooms[room_id].exits[dir];
            ChoiceSpec {
                kind: kind.clone(),
                gates: opt_gate_terms(&exit.gate),
                writes: vec![],
                nav: Some(exit.to_room.clone()),
                label: format!("Go {dir}"),
            }
        }
        ChoiceKind::Objective => ChoiceSpec {
            kind: kind.clone(),
            gates: vec![GateTerm {
                var: item_var(&world.objective.holding),
                op: GateOp::Gte,
                base: 1,
            }],
            writes: vec![Write::set(DUNGEON_WON_VAR.to_string(), 1)],
            nav: None,
            label: format!(
                "Claim the objective, the {} in hand",
                world.objective.holding
            ),
        },
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The compiler.
// ─────────────────────────────────────────────────────────────────────────────

/// Refuse — BY NAME — every construct this compiler does not lower yet. An honest
/// partial compiler: a named [`CompileError::Unsupported`] beats a silent drop.
fn reject_unsupported(world: &GameWorld) -> Result<(), CompileError> {
    let unsupported = |construct: String| Err(CompileError::Unsupported { construct });
    if let Some(h) = world.hostiles.values().next() {
        return unsupported(format!(
            "hostile `{}` (one-shot foes are not lowered yet)",
            h.name
        ));
    }
    if let Some(c) = world.combat.values().next() {
        return unsupported(format!(
            "combat `{}` (HP fights are not lowered yet)",
            c.name
        ));
    }
    if let Some(s) = world.spells.first() {
        return unsupported(format!("spell `{}` (spells are not lowered yet)", s.word));
    }
    if let Some(r) = world.spell_rules.first() {
        return unsupported(format!(
            "spell-rule for `{}` (spells are not lowered yet)",
            r.spell
        ));
    }
    if let Some(c) = world.consumables.first() {
        return unsupported(format!(
            "consumable `{}` (consumables are not lowered yet)",
            c.item
        ));
    }
    if let Some(s) = world.statuses.first() {
        return unsupported(format!(
            "status `{}` (statuses are not lowered yet)",
            s.flag
        ));
    }
    if let Some(l) = &world.light {
        return unsupported(format!(
            "light `{}` (the oil budget is not lowered yet)",
            l.lamp
        ));
    }
    if let Some(l) = world.lose.first() {
        return unsupported(format!(
            "lose condition on `{}` (lose terminals are not lowered yet)",
            l.flag
        ));
    }
    if world.player_max_hp != 0 {
        return unsupported("player_hp (HP combat is not lowered yet)".to_string());
    }
    Ok(())
}

/// One gate term as a spween condition atom.
fn term_expr(term: &GateTerm) -> ConditionExpr {
    ConditionExpr::Atom(ConditionClause::Compare(CompareClause {
        var: term.var.as_str().into(),
        op: term.op.compare_op(),
        value: Value::Int(term.base),
        span: 0..0,
    }))
}

/// A conjunction of gate terms as a spween [`Condition`] (`None` when ungated). Folded
/// LEFT into nested `And`s, which is the shape `lower_expr` walks into a flat
/// constraint list — so `requires A and B and C` installs three teeth on one case.
fn gate_condition(terms: &[GateTerm]) -> Option<Condition> {
    let mut it = terms.iter();
    let first = term_expr(it.next()?);
    let expr = it.fold(first, |acc, t| {
        ConditionExpr::And(Box::new(acc), Box::new(term_expr(t)))
    });
    Some(Condition { expr, span: 0..0 })
}

/// Build the spween [`Scene`] mirroring the world's room graph — constructed as AST
/// (never text), so descriptions/labels can never smuggle syntax into the lowering.
fn build_scene(world: &GameWorld) -> Scene {
    // A content-derived scene id: it drives the deterministic world-cell identity, so
    // two different dungeons never share a cell id at the same seed.
    let digest = blake3::hash(format!("{world:?}").as_bytes());
    let scene_id = format!("dungeon-dsl/{}", digest.to_hex());

    let mut passages = Vec::new();
    for room_id in room_order(world) {
        let room = &world.rooms[&room_id];
        let mut content = Vec::new();
        let prose = if room.description.is_empty() {
            room.name.clone()
        } else {
            format!("{} — {}", room.name, room.description)
        };
        content.push(PassageContent::Prose(Prose {
            text: prose.into(),
            span: 0..0,
        }));
        for kind in room_choice_kinds(world, &room_id) {
            let spec = choice_spec(world, &room_id, &kind);
            let effects = spec
                .writes
                .iter()
                .map(|w| match w.kind {
                    WriteKind::Set(v) => Effect::Set(SetEffect {
                        var: w.var.as_str().into(),
                        value: Value::Int(v),
                        span: 0..0,
                    }),
                    WriteKind::Add(d) => Effect::Modify(ModifyEffect {
                        var: w.var.as_str().into(),
                        delta: d,
                        span: 0..0,
                    }),
                })
                .collect();
            let target = match &spec.nav {
                Some(room) => NavigationTarget {
                    target: room.as_str().into(),
                    is_end: false,
                    span: 0..0,
                },
                None => NavigationTarget {
                    target: "END".into(),
                    is_end: true,
                    span: 0..0,
                },
            };
            content.push(PassageContent::Choice(Choice {
                text: spec.label.into(),
                condition: gate_condition(&spec.gates),
                effects,
                target: Some(target),
                span: 0..0,
            }));
        }
        passages.push(Passage {
            name: room_id.as_str().into(),
            content,
            span: 0..0,
        });
    }

    Scene {
        meta: SceneMeta {
            id: scene_id.into(),
            title: "compiled .dungeon world".into(),
            tags: Vec::new(),
            weight: 1,
            cooldown: 0,
            requires: None,
            custom: Vec::new(),
            span: 0..0,
        },
        passages,
        span: 0..0,
    }
}

/// The freeze tooth for a compiled var key, on whichever plane it landed.
fn freeze_tooth(key: u64) -> StateConstraint {
    if key < STATE_SLOTS as u64 {
        StateConstraint::Immutable { index: key as u8 }
    } else {
        StateConstraint::HeapField {
            key,
            atom: HeapAtom::Immutable,
        }
    }
}

/// The expected executor tooth of a gate term `{ var <op> base }` on a choice whose net
/// additive delta on `var` is `d`, on whichever plane the var landed.
///
/// This mirrors `spween_dregg`'s `compare_constraint` arm-for-arm: a gate is stated over
/// the PRE-state and the executor checks the POST-state, so the threshold shifts by the
/// choice's own delta on that var (`post = pre + d`), flooring at zero exactly as the v0
/// lowering's `thr` does. The `d` term is what makes a SPEND counter checkable: the gate
/// says `pre <= 0` and the installed tooth says `post <= 1`, because the same turn bumps
/// it. Re-derived here from the SOURCE rather than read off the program — a shift this
/// module got wrong would be a `MISSING`/`PHANTOM` build failure, not a silent gate.
fn gate_tooth(key: u64, op: GateOp, base: i64, d: i64) -> StateConstraint {
    let thr = |t: i64| field_from_u64(t.max(0) as u64);
    if key < STATE_SLOTS as u64 {
        let index = key as u8;
        match op {
            GateOp::Gte => StateConstraint::FieldGte {
                index,
                value: thr(base + d),
            },
            GateOp::Lte => StateConstraint::FieldLte {
                index,
                value: thr(base + d),
            },
            GateOp::Eq => StateConstraint::FieldEquals {
                index,
                value: thr(base + d),
            },
        }
    } else {
        let atom = match op {
            GateOp::Gte => HeapAtom::Gte {
                value: thr(base + d),
            },
            GateOp::Lte => HeapAtom::Lte {
                value: thr(base + d),
            },
            GateOp::Eq => HeapAtom::Equals {
                value: thr(base + d),
            },
        };
        StateConstraint::HeapField { key, atom }
    }
}

/// The nav pin: the choice's turn must LAND on its declared target passage, so a
/// stapled `SetField(PASSAGE_SLOT, elsewhere)` on this method is refused.
fn nav_pin(story: &CompiledStory, nav: &Option<String>) -> StateConstraint {
    let idx = match nav {
        Some(room) => *story
            .passage_index
            .get(room)
            .expect("nav target is a compiled passage (compile_scene validated it)")
            as u64,
        None => PASSAGE_ENDED,
    };
    StateConstraint::FieldEquals {
        index: PASSAGE_SLOT as u8,
        value: field_from_u64(idx),
    }
}

/// **Compile a validated [`GameWorld`] into a deployable, translation-validated
/// [`CompiledDungeon`].** Fail-closed at every stage: a validator-broken world, an
/// unsupported construct, and a lowering that does not match the source are all
/// errors — never a degraded success.
pub fn compile_world(world: &GameWorld) -> Result<CompiledDungeon, CompileError> {
    // 1. Only a validator-clean world compiles (a broken dungeon never deploys).
    let errors: Vec<String> = validate(world)
        .into_iter()
        .filter(|i| i.is_error())
        .map(|i| i.message)
        .collect();
    if let Some(first) = errors.first() {
        return Err(CompileError::WorldInvalid {
            first: first.clone(),
            errors: errors.len(),
        });
    }

    // 2. Honest partial coverage: name what we cannot lower, refuse fail-closed.
    reject_unsupported(world)?;

    // 3. The UNTRUSTED lowering: build the scene, hand it to the v0 compiler.
    let scene = build_scene(world);
    let mut story = compile_scene(&scene).map_err(CompileError::Scene)?;

    // 4. AUGMENT: nav pin + write confinement on every case (the staple closure).
    augment(world, &mut story);

    // 5. The mapping tables.
    let mut choices = Vec::new();
    for room_id in room_order(world) {
        for (index, kind) in room_choice_kinds(world, &room_id).into_iter().enumerate() {
            choices.push(LoweredChoice {
                room: room_id.clone(),
                index,
                method: choice_method(&room_id, index),
                kind,
            });
        }
    }
    let compiled = CompiledDungeon {
        rooms: story.passage_index.clone(),
        scene,
        story,
        choices,
    };

    // 6. TRANSLATION VALIDATION: check the output against the source before
    //    returning it. A failing artifact is an error, never a success.
    check_lowering(world, &compiled)?;
    Ok(compiled)
}

/// Augment the compiled program with the staple-closure teeth: on each choice case a
/// nav pin + freezes for every var the choice does not write; on the genesis case
/// freezes for every var (genesis writes only the passage bind + the one-shot
/// sentinel). The heap-hatch case already freezes all registers + compiled ext keys.
fn augment(world: &GameWorld, story: &mut CompiledStory) {
    // Dispatch symbol → (writes, nav) for every choice method.
    let mut per_method: BTreeMap<[u8; 32], (BTreeSet<String>, Option<String>)> = BTreeMap::new();
    for room_id in room_order(world) {
        for (index, kind) in room_choice_kinds(world, &room_id).into_iter().enumerate() {
            let spec = choice_spec(world, &room_id, &kind);
            per_method.insert(
                symbol(&choice_method(&room_id, index)),
                (
                    spec.writes.iter().map(|w| w.var.clone()).collect(),
                    spec.nav,
                ),
            );
        }
    }
    let genesis = symbol(GENESIS_METHOD);
    let all_vars: Vec<(String, u64)> = story
        .var_slots
        .iter()
        .map(|(name, &key)| (name.clone(), key))
        .collect();
    let nav_pins: BTreeMap<[u8; 32], StateConstraint> = per_method
        .iter()
        .map(|(m, (_, nav))| (*m, nav_pin(story, nav)))
        .collect();

    let CellProgram::Cases(cases) = &mut story.program else {
        unreachable!("compile_scene always emits CellProgram::Cases");
    };
    for case in cases.iter_mut() {
        let TransitionGuard::MethodIs { method } = &case.guard else {
            continue;
        };
        if let Some((writes, _)) = per_method.get(method) {
            case.constraints.push(nav_pins[method].clone());
            for (var, key) in &all_vars {
                if !writes.contains(var) {
                    case.constraints.push(freeze_tooth(*key));
                }
            }
        } else if *method == genesis {
            for (_, key) in &all_vars {
                case.constraints.push(freeze_tooth(*key));
            }
        }
        // The heap-hatch case is left exactly as the v0 compiler emitted it.
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Translation validation.
// ─────────────────────────────────────────────────────────────────────────────

/// Render a constraint multiset canonically (sorted debug strings) for comparison.
fn canon(constraints: &[StateConstraint]) -> Vec<String> {
    let mut v: Vec<String> = constraints.iter().map(|c| format!("{c:?}")).collect();
    v.sort();
    v
}

/// The genesis-sentinel freeze every non-genesis case carries (from the v0 compiler).
fn sentinel_freeze() -> StateConstraint {
    StateConstraint::HeapField {
        key: GENESIS_DONE_EXT_KEY,
        atom: HeapAtom::Immutable,
    }
}

/// **The translation-validation check** — compare the INSTALLED program against the
/// SOURCE ruleset, both directions. For every gate the source declares on an
/// exit/topic/use/objective there must be the corresponding executor tooth in that
/// choice's case (resolved by NAME through the compiled layout); and for every
/// constraint in the program there must be a source construct or documented
/// augmentation accounting for it — no missing teeth, no phantom teeth, no
/// unrecognized cases. Any mismatch is a named [`CompileError::ValidationFailed`].
///
/// Public so a caller (or an adversarial test) can re-check any artifact — including
/// one whose program was tampered with after compile.
pub fn check_lowering(world: &GameWorld, d: &CompiledDungeon) -> Result<(), CompileError> {
    let fail = |mismatch: String| Err(CompileError::ValidationFailed { mismatch });

    // Resolve a compiled var BY NAME — a gate over a var with no compiled key means
    // the lowering dropped state the source depends on.
    let var_key = |var: &str| -> Result<u64, CompileError> {
        d.story
            .var_slots
            .get(var)
            .copied()
            .ok_or_else(|| CompileError::ValidationFailed {
                mismatch: format!("compiled layout has no key for source var `{var}`"),
            })
    };

    // Expected case set, derived from the SOURCE (fresh enumeration — not d.choices).
    let mut expected: BTreeMap<[u8; 32], (String, Vec<StateConstraint>)> = BTreeMap::new();
    let all_vars: Vec<(String, u64)> = d
        .story
        .var_slots
        .iter()
        .map(|(name, &key)| (name.clone(), key))
        .collect();

    // Every room must be a compiled passage (checked up front, so nav-pin
    // derivation below can never dereference a missing passage).
    for room_id in room_order(world) {
        if !d.story.passage_index.contains_key(&room_id) {
            return fail(format!("room `{room_id}` has no compiled passage"));
        }
    }

    for room_id in room_order(world) {
        for (index, kind) in room_choice_kinds(world, &room_id).into_iter().enumerate() {
            let spec = choice_spec(world, &room_id, &kind);
            let method = choice_method(&room_id, index);
            let mut teeth = Vec::new();
            for term in &spec.gates {
                // The choice's OWN delta on the gated var — `None` iff the spec assigns
                // it, which the v0 compiler cannot lift. Refuse the build rather than
                // ship a choice whose gate silently fell through to the handler.
                let Some(delta) = spec.delta_on(&term.var) else {
                    return fail(format!(
                        "case `{method}` ({kind:?} in `{room_id}`) gates on `{}` and also ASSIGNS it — \
                         a gate over an overwritten var does not lower to an executor tooth (use `+=`)",
                        term.var
                    ));
                };
                teeth.push(gate_tooth(var_key(&term.var)?, term.op, term.base, delta));
            }
            if !spec.gates.is_empty() {
                // Every gate must have lowered FULLY to executor constraints — a
                // handler-only clause is not an enforced gate. With a CONJUNCTION this
                // is the tooth that catches a partially-lowered `A and B`: the v0
                // compiler clears the flag for the whole choice if any conjunct is
                // un-lowerable, so `A and B` can never deploy as just `A`.
                if d.story.fully_gated.get(&method) != Some(&true) {
                    return fail(format!(
                        "gate on `{method}` ({kind:?} in `{room_id}`) did not fully lower to executor constraints"
                    ));
                }
            }
            teeth.push(sentinel_freeze());
            teeth.push(nav_pin(&d.story, &spec.nav));
            let writes = spec.written();
            for (var, key) in &all_vars {
                if !writes.contains(var) {
                    teeth.push(freeze_tooth(*key));
                }
            }
            expected.insert(symbol(&method), (method, teeth));
        }
    }

    // The genesis case: the one-shot sentinel teeth + every var frozen.
    let mut genesis_teeth = vec![
        StateConstraint::HeapField {
            key: GENESIS_DONE_EXT_KEY,
            atom: HeapAtom::Equals {
                value: field_from_u64(1),
            },
        },
        StateConstraint::HeapField {
            key: GENESIS_DONE_EXT_KEY,
            atom: HeapAtom::DeltaEquals { d: 1 },
        },
    ];
    for (_, key) in &all_vars {
        genesis_teeth.push(freeze_tooth(*key));
    }
    expected.insert(
        symbol(GENESIS_METHOD),
        (GENESIS_METHOD.to_string(), genesis_teeth),
    );

    // The heap-hatch case: every register frozen + every compiled ext key frozen +
    // the sentinel freeze (exactly what the v0 compiler emits).
    let mut hatch_teeth: Vec<StateConstraint> = (0..STATE_SLOTS)
        .map(|index| StateConstraint::Immutable { index: index as u8 })
        .collect();
    for key in d.story.ext_keys() {
        hatch_teeth.push(StateConstraint::HeapField {
            key,
            atom: HeapAtom::Immutable,
        });
    }
    hatch_teeth.push(sentinel_freeze());
    expected.insert(
        symbol(HEAP_HATCH_METHOD),
        (HEAP_HATCH_METHOD.to_string(), hatch_teeth),
    );

    // Compare against the INSTALLED program, both directions.
    let CellProgram::Cases(cases) = &d.story.program else {
        return fail("installed program is not CellProgram::Cases".to_string());
    };
    let mut seen: BTreeSet<[u8; 32]> = BTreeSet::new();
    for case in cases {
        let TransitionGuard::MethodIs { method } = &case.guard else {
            return fail(format!(
                "program carries a non-method-dispatch case (guard {:?}) no source construct authorizes",
                case.guard
            ));
        };
        let Some((name, teeth)) = expected.get(method) else {
            return fail(
                "program carries a case for a method no source construct names (a phantom case)"
                    .to_string(),
            );
        };
        if !seen.insert(*method) {
            return fail(format!("duplicate case for method `{name}`"));
        }
        let want = canon(teeth);
        let got = canon(&case.constraints);
        if want != got {
            // Name the first missing / phantom tooth precisely.
            if let Some(missing) = want.iter().find(|t| !got.contains(t)) {
                return fail(format!(
                    "case `{name}` is MISSING the expected tooth {missing} (source gate/pin without its executor constraint)"
                ));
            }
            if let Some(phantom) = got.iter().find(|t| !want.contains(t)) {
                return fail(format!(
                    "case `{name}` carries a PHANTOM constraint {phantom} no source construct accounts for"
                ));
            }
            return fail(format!(
                "case `{name}` constraint multiset mismatch (duplicate-count drift): expected {want:?}, got {got:?}"
            ));
        }
    }
    for (m, (name, _)) in &expected {
        if !seen.contains(m) {
            return fail(format!("no case installed for expected method `{name}`"));
        }
    }
    Ok(())
}
