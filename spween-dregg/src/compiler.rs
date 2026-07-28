//! # spween → cell compiler (v0)
//!
//! Lowers a parsed spween [`Scene`] into a deployable dregg **world-cell descriptor**:
//! a slot layout (passages/vars → cell slots) and a [`CellProgram`] whose
//! per-choice cases encode each `Choice.condition` as an **executor-enforced
//! predicate**. After deploy, a choice's gate is not a client-side courtesy —
//! it is a `dregg_cell::CellProgram` case the verified executor re-checks on the
//! choice-turn's post-state, so a client cannot present an ineligible choice as
//! taken (SPWEEN-ON-DREGG §3, property 3).
//!
//! ## The slot layout — and the WIDE PLANE past the 16th
//!
//! * slot [`PASSAGE_SLOT`] (0): the current passage index (the `RuntimeState`
//!   control-flow position, made cell state). [`PASSAGE_ENDED`] marks a finished
//!   scene.
//! * slots `1..`: one per numeric/bool variable named in a condition or effect,
//!   then one per `category.key` membership atom. Assignment is deterministic
//!   (sorted names) so a re-compile of the same scene yields the same layout.
//! * **keys [`SPILL_EXT_BASE`]`..`: the overflow.** The cell has 16 fixed registers
//!   ([`STATE_SLOTS`]), so slot 0 + 15 named atoms fill it. A scene naming MORE does
//!   NOT fail — the 16th and every later atom SPILLS to an **ext key**, an unbounded
//!   `key >= STATE_SLOTS` that `Effect::SetField` routes into the cell's COMMITTED
//!   `fields_map` (digested into `fields_root`, folded into the cell commitment). The
//!   spill is a suffix of the same deterministic order, so the first 15 named atoms of
//!   a wide scene land in exactly the registers they would have had, and a scene that
//!   fits (`<= 15`) compiles BYTE-IDENTICALLY to before — no ext key, no new tooth.
//!
//! ### Resolve BY NAME, never by a guessed index
//!
//! [`CompiledStory::var_slots`] / [`CompiledStory::has_slots`] are the name→**key**
//! mapping: a value `< STATE_SLOTS` is a fixed register, `>= STATE_SLOTS` is an ext
//! key. Consumers MUST look a var up by name ([`CompiledStory::var_key`]) — a
//! hardcoded index that happens to be right for a narrow scene points at the WRONG
//! atom in a wide one (a prior lane found that naively repointing hardcoded indices
//! INVERTS gates). [`CompiledStory::is_spilled`] answers "which plane is it on".
//!
//! ### What the ext plane costs (design against these — they are not hidden)
//!
//! * **O(n) per ext write.** `CellState::set_field_ext` rebuilds the ENTIRE
//!   `fields_root` (sorted-Poseidon2 over every map entry) on every write — there is no
//!   incremental cache (unlike the heap's `HeapTreeCache`). A register write is O(1).
//!   This is why the first 15 atoms stay in registers: the fast plane is filled first.
//! * **~31-bit per-value binding.** Each `fields_root` leaf folds its 32-byte value to
//!   ONE ~31-bit BabyBear felt. The root is ~124-bit (8 felts) and the `fields_map`
//!   holds the full 32 bytes the teeth read, but the per-value BINDING in the committed
//!   root is the known ~31-bit umem boundary. A story var is a small counter, so the
//!   projection ([`crate::value_to_u64`]) is well inside it — but the boundary is real.
//! * **Executor-enforced, NOT in-circuit-proven.** The ext-plane atoms
//!   (`HeapField`/`HeapFieldLteOther`) are evaluated by the host scalar evaluator
//!   (`cell::program::eval`); the slot-caveat PI vector cannot express a heap key, so
//!   they carry NO AIR teeth (`turn/src/executor/mod.rs`). A register `FieldGte` DOES
//!   project into the circuit. Both are re-checked by the real executor on every turn —
//!   which is exactly what an executor-refereed game needs — but a spilled gate must
//!   NOT be described as in-circuit-proven.
//!
//! ### Same teeth on both planes
//!
//! Every gate a register var lowers to has an ext-plane equal, so a var that spills
//! keeps its bite (`FieldGte`→`HeapField{Gte}`, `FieldLte`→`{Lte}`,
//! `FieldEquals`→`{Equals}`, the clamp-companion `FieldDelta`→`{DeltaEquals}`,
//! cross-var `FieldLteOther`→`HeapFieldLteOther`). The ext atoms are STRICTER in one
//! way: on the heap, **absent ≠ present-zero** — a `HeapField` over an unwritten key
//! REFUSES. A register is born present-zero, so to keep the two planes'
//! semantics identical [`crate::WorldCell`] BIRTHS every compiled ext key at
//! field-zero on deploy (the same setup write `seed_var` uses). Without that, an
//! unseeded spilled var would refuse gates its register twin admits — a play-vs-replay
//! split.
//!
//! ## The gate lowering (a condition → a post-state predicate)
//!
//! A choice's `condition` is checked against the *pre*-state, but a
//! [`StateConstraint`] bites on the *post*-state. Because the compiler knows a
//! choice's own effects at compile time, it lifts a pre-state gate to an
//! equivalent post-state one: for a gate var with net additive delta `d` from the
//! choice's effects, `pre ≥ T  ⟺  post ≥ T + d` (the choice does not otherwise
//! touch the var). A gate whose var is *`Set`* by the same choice (post is a
//! constant, independent of pre) cannot be lifted — that clause is left to the
//! runtime/handler gate and no executor constraint is emitted for it. `Compare`
//! against a string/float literal is likewise handler-only in v0. The numeric/bool
//! gates (`courage >= 5`, `gold >= 100`, `inventory.key`) lower to real executor teeth.
//!
//! ## VAR-OP-VAR gates (a cross-variable tooth)
//!
//! A comparison whose RHS is another VARIABLE (`{ gold >= "$price" }`, `{ hp <= "$cap"
//! }`) lowers to a real CROSS-SLOT tooth — [`StateConstraint::FieldLteOther`]
//! (`new[a] <= new[b] + delta`) — instead of falling back to the handler gate, so a
//! cross-variable gate BITES on the verified executor (a broke buyer whose `gold` is
//! below the dynamic `price` is REFUSED, not merely hidden client-side). The current
//! git-pinned spween grammar parses a comparison's RHS only as a literal, so the
//! var-reference rides the closest expressible form — a quoted string with a `$` sigil
//! (see [`var_ref`]); a native `var op var` is the noted parser follow-up. See
//! [`cross_var_teeth`] for the pre→post lift and its clamp guard.
//!
//! ## The clamp caveat (why a same-var decrement needs an exact-delta companion)
//!
//! The `pre ≥ T ⟺ post ≥ T+d` identity assumes the choice applies its delta
//! *exactly*: `post = pre + d`. But the executor CLAMPS a `Modify` at zero
//! (`post = max(0, pre + d)`, so `hp -= dmg` never underflows). When the choice
//! DECREMENTS the gate var (`d < 0`) and the shifted threshold lands `≤ 0`, that
//! clamp collapses the lifted gate to a vacuous `≥ 0`: `{ gold >= 50 } ~ gold -= 50`
//! lifts to `FieldGte(gold, 0)`, ALWAYS TRUE — a broke buyer's purchase clamps the
//! purse to `0 ≥ 0` and commits (goods delivered, purse silently zeroed). For
//! exactly those clamp-defeated gates (see `lift_defeated_by_clamp`) we PIN the
//! delta with a companion [`StateConstraint::FieldDelta`]`{ index, d }`: a clamped
//! underflow lands `0 ≠ old + d` (u64 lane, wrapping) and is REFUSED, so the
//! pre-gate bites exactly. When the shifted threshold stays `> 0` the comparison
//! itself catches an underflow (`{ hp >= 21 } ~ hp -= 20` ⇒ `FieldGte(hp, 1)`), so
//! NO companion is emitted — a case whose delta is overridden at runtime (dice
//! combat reuses that same case with a *rolled* hp delta) is not over-pinned. A
//! gate on a var the choice does not touch (`d = 0`) is unchanged.

use std::collections::BTreeMap;

use dregg_app_framework::{
    CellProgram, FieldElement, StateConstraint, TransitionCase, TransitionGuard, field_from_u64,
    symbol,
};
use dregg_cell::program::{HeapAtom, SimpleStateConstraint};
use spween::{
    CompareOp, Condition, ConditionClause, ConditionExpr, Effect, PassageContent, Scene, Value,
};

use crate::encoding::value_to_u64;

/// The cell slot holding the current passage index (the story's program counter).
pub const PASSAGE_SLOT: usize = 0;

/// Sentinel value stored in [`PASSAGE_SLOT`] when the scene has ended (`-> END` or
/// a choice with no navigation target). Distinct from any real passage index.
pub const PASSAGE_ENDED: u64 = 0xFFFF_FFFF;

/// The number of cell state slots available. This **IS** `dregg_cell::state::STATE_SLOTS`
/// — the same item, re-exported, not a mirrored literal: two constants that agree today
/// are two constants that disagree later, and this one is the bound the executor's own
/// register/heap routing uses. A heap-keyed write ([`WorldCell::apply_raw`]) targets an
/// index `>= STATE_SLOTS`.
pub use dregg_cell::state::STATE_SLOTS;

/// **The base ext key the compiler SPILLS a scene's 16th-and-beyond atom to.** Once
/// the 16 fixed registers are full, [`compile_scene`] allocates `SPILL_EXT_BASE`,
/// `SPILL_EXT_BASE + 1`, … — keys `>= STATE_SLOTS`, which `Effect::SetField` routes
/// into the cell's committed `fields_map` / `fields_root` rather than the register
/// file. Unbounded, so a scene's variable count is not a compile ceiling.
///
/// Keyed at `2^34` — ABOVE both reserved ext keys in play (`REFUSAL_AUDIT_EXT_KEY =
/// 2^32` in `dregg_cell::state`, [`crate::DECISION_EXT_KEY`] `= 2^33`) and far above
/// the small `STATE_SLOTS + n` keys an app's own heap collection uses via
/// [`crate::WorldCell::apply_raw`] — so a spilled story var can never collide with a
/// reserved key or with an application collection.
///
/// Keys are carried as canonical `u64`s through [`CompiledStory::var_slots`] and
/// `Effect::SetField`, so this layout is byte-identical on wasm32 and native hosts.
pub const SPILL_EXT_BASE: u64 = 0x0000_0004_0000_0000;

/// The deterministic key allocator: fill the fast fixed registers first, then spill
/// to the ext plane. See the module docs — the order is a SUFFIX split of the same
/// sorted sequence, so a scene that fits gets exactly its old layout.
struct KeyAlloc {
    /// The next free register slot (`PASSAGE_SLOT + 1 ..= STATE_SLOTS`).
    next_slot: u64,
    /// How many ext keys have been handed out.
    spilled: u64,
}

impl KeyAlloc {
    fn new() -> Self {
        KeyAlloc {
            next_slot: (PASSAGE_SLOT + 1) as u64,
            spilled: 0,
        }
    }

    /// The next key: a register while any remain, then an ext key.
    fn take(&mut self) -> u64 {
        if self.next_slot < STATE_SLOTS as u64 {
            let k = self.next_slot;
            self.next_slot += 1;
            k
        } else {
            let k = SPILL_EXT_BASE + self.spilled;
            self.spilled += 1;
            k
        }
    }
}

/// Which plane a compiled key lives on — the one place the register/ext split is
/// decided, so every lowering below reads it the same way.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Plane {
    /// A fixed register slot: the fast, in-circuit-projected plane.
    Slot(u8),
    /// An ext key in the committed `fields_map`: unbounded, host-evaluated.
    Ext(u64),
}

/// The plane a compiled key names (the SAME `< STATE_SLOTS` test the executor's
/// `apply_set_field` and `CellState::get_field_ext` use to route a key).
fn plane_of(key: u64) -> Plane {
    if key < STATE_SLOTS as u64 {
        Plane::Slot(key as u8)
    } else {
        Plane::Ext(key)
    }
}

impl Plane {
    /// The uniform u64 key — what `CellState::get_field_ext` takes on EITHER plane
    /// (`< STATE_SLOTS` resolves to the register file). Lets a cross-plane relation
    /// (`HeapFieldLteOther`) name a register operand and an ext operand alike.
    fn key(self) -> u64 {
        match self {
            Plane::Slot(i) => i as u64,
            Plane::Ext(k) => k,
        }
    }
}

/// The dispatch method a choice's turn presents — the key its executor-enforced
/// gate case is guarded by. Used by BOTH the compiler (to name the case) and the
/// driver (to name the action), so they always agree.
pub fn choice_method(passage: &str, choice_index: usize) -> String {
    format!("c/{passage}/{choice_index}")
}

/// The dispatch method the genesis turn (the intro passage's entry effects +
/// initial passage-slot bind) presents.
pub const GENESIS_METHOD: &str = "genesis";

/// **The reserved genesis-done sentinel key — the tooth that makes `genesis`
/// ONE-SHOT.**
///
/// ## The hole this closes (the root, not a per-slot patch)
///
/// [`compile_scene`] must emit a `MethodIs { genesis }` case (the executor's
/// dispatch is method-default-deny, so the genesis turn needs a case to land on).
/// Before this key that case carried EMPTY constraints and [`crate::WorldCell::apply_raw`]
/// re-dispatches ANY method with no one-shot guard — so a POST-DEPLOY
/// `apply_raw("genesis", [SetField(slot, V)])` re-hit the permissive genesis case
/// and committed arbitrary writes to ANY slot, routing around every choice gate. That
/// is a UNIVERSAL WRITE-HATCH on every compiled scene (dungeon/story/quest/dialogue),
/// closed per-slot ~14 times; this closes it at the ROOT for every slot at once.
///
/// ## The mechanism (a `0 → 1` transition, admissible exactly once)
///
/// The genesis case's teeth become the CONJUNCTION
/// `HeapField{Equals 1} ∧ HeapField{DeltaEquals 1}` over THIS key, which holds iff
/// `old == 0 ∧ new == 1` — the sentinel goes `0 → 1`. [`crate::WorldCell`] births it
/// at field-zero on deploy and the genesis turn writes it to `1` (injected in
/// `WorldCell::commit` for the `genesis` method), so the LEGIT one-time deploy/seed
/// passes. Every LATER genesis turn reads `old == 1`, where `new == 1` (Equals) forces
/// `Δ == 0 ≠ 1` (DeltaEquals) and `new == 2` (Δ == 1) forces `new ≠ 1` (Equals) — the
/// two teeth are jointly unsatisfiable, so genesis is REFUSED regardless of which
/// slot a stapled `SetField` targets, with NO per-slot `SlotChanged` dependence.
///
/// Every NON-genesis case (each choice case + the [`HEAP_HATCH_METHOD`] case) additionally
/// freezes this key with `HeapField{Immutable}`, so no other method — not an ungated
/// choice with permissive teeth, not the heap hatch — can RESET the sentinel to `0` and
/// re-open genesis. The genesis case itself carries no `Immutable` (it must perform the
/// `0 → 1` write).
///
/// Keyed at `2^33 + 1` — distinct from [`crate::DECISION_EXT_KEY`] (`2^33`), above
/// `REFUSAL_AUDIT_EXT_KEY` (`2^32`) and far below [`SPILL_EXT_BASE`] (`2^34`), so it can
/// never collide with a spilled story var, a reserved key, or a small `STATE_SLOTS + n`
/// application-collection key.
/// `Effect::SetField::index` is a canonical `u64`, so this key is represented
/// identically on wasm32 and native hosts. The old platform-sized encoding
/// truncated this value to register `1` in browsers and made every genesis turn
/// overwrite an ordinary game field.
pub const GENESIS_DONE_EXT_KEY: u64 = 0x0000_0000_7000_0011;

/// The reserved dispatch method a raw HEAP-hatch turn ([`WorldCell::apply_raw`] with
/// heap-keyed effects) presents.
///
/// ## Why a reserved method, not an `Always` catch-all
///
/// The executor's `CellProgram::Cases` dispatch is **method-default-deny**: once a
/// program has ANY method-binding (`MethodIs`) case, an action whose method matches
/// none of them is `NoTransitionCaseMatched` — *even if a separate `Always`-guarded
/// case still matches* (`TransitionGuard::is_method_dispatching` returns `false` for
/// `Always`, so an `Always` case never satisfies the "some dispatch case matched"
/// requirement). So a plain `Always` catch-all does **not** revive the hatch: a raw
/// heap turn under a novel method is still refused. Nor can the catch-all key on the
/// effect *kind* (`EffectKindIs { SetField }`), because a choice-turn is *also* a
/// `SetField` — an effect-kind catch-all would either absorb forged choice methods
/// (a dispatch hole) or, if it carried register-slot teeth, refuse the real choices
/// it AND-matches. The heap-vs-slot distinction the hatch needs (write target
/// `index >= STATE_SLOTS`) is not exposed to any dispatch guard.
///
/// So the hatch gets its own reserved `MethodIs { HEAP_HATCH_METHOD }` case whose
/// teeth freeze every register slot (`Immutable`), CONFINING the turn to the heap: a
/// legal heap-keyed write DISPATCHES (admitted iff the heap teeth pass), a forged
/// hatch turn that overwrites a register slot (e.g. `PASSAGE_SLOT` to teleport) is
/// REFUSED by the confinement teeth, and any UNKNOWN method (not a choice, not
/// genesis, not this) is still refused by its own case's absence — the dispatch
/// default-deny is not weakened.
pub const HEAP_HATCH_METHOD: &str = "spween/heap";

/// A story lowered to a world-cell descriptor: the slot layout, the passage index,
/// and the installed [`CellProgram`].
#[derive(Clone, Debug)]
pub struct CompiledStory {
    /// The scene id (drives the deterministic world-cell identity).
    pub scene_id: String,
    /// **Variable name → cell FIELD KEY** (numeric/bool projection). Every variable
    /// named in a condition or a Set/Modify effect gets a key: a fixed register
    /// (`< STATE_SLOTS`) while any remain, then an ext key
    /// (`>= `[`SPILL_EXT_BASE`], the committed `fields_map`). Resolve BY NAME
    /// ([`Self::var_key`]) — a hardcoded index is wrong the moment a scene widens.
    pub var_slots: BTreeMap<String, u64>,
    /// `(category, key)` membership atom → cell FIELD KEY (1 = present, 0 = absent).
    /// Same two planes as [`Self::var_slots`]; membership is allocated after the vars,
    /// so it is what spills first.
    pub has_slots: BTreeMap<(String, String), u64>,
    /// Passage name → index (matches `spween::Runtime`'s enumerate order).
    pub passage_index: BTreeMap<String, usize>,
    /// The installed program: one method-guarded case per choice + a genesis case.
    pub program: CellProgram,
    /// Per gated choice, whether the gate lowered FULLY to executor constraints
    /// (`true`) or leans on the runtime/handler for some clause (`false`). Keyed by
    /// the choice method. Absent ⇒ the choice is ungated.
    pub fully_gated: BTreeMap<String, bool>,
}

impl CompiledStory {
    /// **The name→key resolution.** The cell field key holding `name`'s numeric
    /// projection, or `None` if the scene never named it. THE way to reach a var: a
    /// guessed index is right only for the layout you guessed against.
    pub fn var_key(&self, name: &str) -> Option<u64> {
        self.var_slots.get(name).copied()
    }

    /// The cell field key holding the `category.key` membership atom.
    pub fn has_key(&self, category: &str, key: &str) -> Option<u64> {
        self.has_slots
            .get(&(category.to_string(), key.to_string()))
            .copied()
    }

    /// Whether `name` SPILLED to the ext plane (the committed `fields_map`) rather
    /// than a fixed register — i.e. whether its gates are host-evaluated
    /// `HeapField` atoms and its writes pay the O(n) `fields_root` rebuild. `false`
    /// for a register var AND for a name the scene never used.
    pub fn is_spilled(&self, name: &str) -> bool {
        self.var_key(name).is_some_and(|k| k >= STATE_SLOTS as u64)
    }

    /// Every ext key this story compiled to (vars + membership), ascending and
    /// deduplicated. The keys [`crate::WorldCell`] births at field-zero on deploy,
    /// freezes against the heap hatch, and folds into its replay snapshot. Empty for
    /// a scene that fits the 16 registers — the whole ext plane is then inert.
    pub fn ext_keys(&self) -> Vec<u64> {
        ext_keys_of(&self.var_slots, &self.has_slots)
    }
}

/// The ascending, deduplicated ext keys of a layout — the shared body of
/// [`CompiledStory::ext_keys`] and the hatch-confinement teeth [`compile_scene`]
/// emits (which needs them before the story exists).
fn ext_keys_of(
    var_slots: &BTreeMap<String, u64>,
    has_slots: &BTreeMap<(String, String), u64>,
) -> Vec<u64> {
    let mut keys: Vec<u64> = var_slots
        .values()
        .chain(has_slots.values())
        .filter(|&&k| k >= STATE_SLOTS as u64)
        .copied()
        .collect();
    keys.sort_unstable();
    keys.dedup();
    keys
}

/// Why a scene could not be compiled to a world-cell.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CompileError {
    /// The scene needs more variable/membership slots than the cell has.
    ///
    /// **No longer produced by [`compile_scene`].** The 16-register budget was never
    /// the cell's capacity — it is the fast plane's size. A scene past it now SPILLS
    /// to the ext plane ([`SPILL_EXT_BASE`]) instead of failing, so there is no
    /// variable-count ceiling to report. The variant is retained so an exhaustive
    /// match on this public enum keeps compiling.
    TooManySlots { needed: usize, available: usize },
    /// A choice navigates to a passage that does not exist in the scene.
    UnknownTarget { target: String },
}

impl std::fmt::Display for CompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CompileError::TooManySlots { needed, available } => write!(
                f,
                "scene needs {needed} state slots but the cell has {available}"
            ),
            CompileError::UnknownTarget { target } => {
                write!(f, "choice navigates to unknown passage `{target}`")
            }
        }
    }
}

impl std::error::Error for CompileError {}

/// The net effect of a choice's effects on one variable.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Delta {
    /// The var is only `Modify`ed; `post = pre + n`. A pre-gate lifts to a post-gate.
    Add(i64),
    /// The var is `Set` to a constant; `post` is independent of `pre` — a pre-gate
    /// cannot be lifted to a post-gate. That clause stays handler-only.
    Overwritten,
}

/// **Compile a spween [`Scene`] into a world-cell descriptor.**
pub fn compile_scene(scene: &Scene) -> Result<CompiledStory, CompileError> {
    // Passage index — matches spween::Runtime's `passages.iter().enumerate()`.
    let passage_index: BTreeMap<String, usize> = scene
        .passages
        .iter()
        .enumerate()
        .map(|(i, p)| (p.name.to_string(), i))
        .collect();

    // Discover every variable and membership atom the scene touches.
    let mut var_names: std::collections::BTreeSet<String> = Default::default();
    let mut has_atoms: std::collections::BTreeSet<(String, String)> = Default::default();
    for passage in &scene.passages {
        for content in &passage.content {
            match content {
                PassageContent::Choice(c) => {
                    if let Some(cond) = &c.condition {
                        collect_condition(cond, &mut var_names, &mut has_atoms);
                    }
                    for e in &c.effects {
                        collect_effect(e, &mut var_names);
                    }
                }
                PassageContent::Effect(e) => collect_effect(e, &mut var_names),
                PassageContent::Prose(_) => {}
            }
        }
    }

    // Deterministic key assignment: passage slot 0, then vars, then membership — the
    // fast fixed registers first, then the ext plane. The `BTreeSet` iteration order
    // (alphabetical) is LOAD-BEARING: it is what makes a re-compile of the same scene
    // reproduce the same layout, which the deterministic-world / replay teeth lean on.
    // The wide plane changes only WHERE the sequence lands past the 15th atom, never
    // the sequence — so a scene that fits gets byte-identically its old layout.
    let mut var_slots = BTreeMap::new();
    let mut has_slots = BTreeMap::new();
    let mut alloc = KeyAlloc::new();
    for name in &var_names {
        var_slots.insert(name.clone(), alloc.take());
    }
    for atom in &has_atoms {
        has_slots.insert(atom.clone(), alloc.take());
    }

    // One method-guarded case per choice (default-deny requires every choice-turn's
    // method to match a case), plus the ONE-SHOT genesis case. The genesis case's teeth
    // are the `0 → 1` transition on [`GENESIS_DONE_EXT_KEY`] (see its docs): admissible
    // exactly once (at deploy, when the sentinel is still field-zero), REFUSED for every
    // post-deploy genesis turn regardless of which slot a stapled `SetField` targets —
    // closing the universal genesis write-hatch at the root, no per-slot dependence.
    let mut cases = vec![TransitionCase {
        guard: TransitionGuard::MethodIs {
            method: symbol(GENESIS_METHOD),
        },
        constraints: genesis_oneshot_teeth(),
    }];
    let mut fully_gated = BTreeMap::new();

    for passage in &scene.passages {
        // Validate navigation targets while we are here.
        let mut choice_idx = 0usize;
        for content in &passage.content {
            let PassageContent::Choice(choice) = content else {
                continue;
            };
            if let Some(nav) = &choice.target {
                if !nav.is_end && !passage_index.contains_key(nav.target.as_str()) {
                    return Err(CompileError::UnknownTarget {
                        target: nav.target.to_string(),
                    });
                }
            }
            let method = choice_method(&passage.name, choice_idx);
            let (mut constraints, full) = lower_gate(
                choice.condition.as_ref(),
                &choice.effects,
                &var_slots,
                &has_slots,
            );
            if choice.condition.is_some() {
                fully_gated.insert(method.clone(), full);
            }
            // FREEZE the genesis-done sentinel on every choice turn: a choice never
            // touches it (its effects write only compiled var keys / the passage slot),
            // so `Immutable` admits the unchanged key — but a stapled
            // `apply_raw("c/…", [SetField(GENESIS_DONE, 0)])` that tried to RESET it (to
            // re-open the one-shot genesis) is REFUSED even when the choice is ungated
            // (empty gate teeth). This is what keeps the genesis one-shot from depending
            // on any per-choice gate.
            constraints.push(genesis_sentinel_freeze());
            cases.push(TransitionCase {
                guard: TransitionGuard::MethodIs {
                    method: symbol(&method),
                },
                constraints,
            });
            choice_idx += 1;
        }
    }

    // The heap escape hatch ([`WorldCell::apply_raw`]): a reserved method-binding case
    // so a raw HEAP-keyed turn DISPATCHES (satisfying the executor's method
    // default-deny) instead of refusing as `NoTransitionCaseMatched`. Its teeth freeze
    // every register slot, confining the hatch to the committed heap (keys
    // `>= STATE_SLOTS`); see [`HEAP_HATCH_METHOD`] for why this is a reserved `MethodIs`
    // case and not an `Always` / `EffectKindIs` catch-all.
    let mut hatch: Vec<StateConstraint> = (0..STATE_SLOTS)
        .map(|index| StateConstraint::Immutable { index: index as u8 })
        .collect();
    // ...AND freeze every key the story SPILLED there. The register freeze alone used
    // to confine the hatch completely, because no story state lived on the heap. With
    // the wide plane it does: without this, a wide scene's `gold` would be a key the
    // hatch — a method any capability-holder can present — could overwrite at will,
    // routing around every gate. That would be a confinement hole OPENED by spilling,
    // so the confinement widens with the story: the hatch reaches the heap keys the
    // story does NOT own, exactly as before, and nothing else.
    //
    // `HeapAtom::Immutable` is "first write free (absent old), then pinned" — and
    // `WorldCell` births every compiled ext key at field-zero on deploy, so the old is
    // always present and the pin always bites. (If a caller reached the evaluator with
    // no old state at all, the heap atom's absent-old arm would admit — but the
    // register `Immutable` teeth in this SAME case surface
    // `TransitionCheckRequiresOldState` there, so the case still fails closed.)
    for key in ext_keys_of(&var_slots, &has_slots) {
        hatch.push(StateConstraint::HeapField {
            key,
            atom: HeapAtom::Immutable,
        });
    }
    // ...AND freeze the genesis-done sentinel here too, so the heap hatch (a method any
    // capability-holder can present) cannot RESET it to re-open the one-shot genesis.
    hatch.push(genesis_sentinel_freeze());
    cases.push(TransitionCase {
        guard: TransitionGuard::MethodIs {
            method: symbol(HEAP_HATCH_METHOD),
        },
        constraints: hatch,
    });

    Ok(CompiledStory {
        scene_id: scene.meta.id.to_string(),
        var_slots,
        has_slots,
        passage_index,
        program: CellProgram::Cases(cases),
        fully_gated,
    })
}

/// The ONE-SHOT genesis teeth: the `0 → 1` transition on [`GENESIS_DONE_EXT_KEY`].
/// `Equals{1} ∧ DeltaEquals{1}` holds iff `old == 0 ∧ new == 1` — admissible exactly
/// once (at deploy, sentinel still field-zero), jointly UNSATISFIABLE for every
/// post-deploy genesis turn (`old == 1` forces `Δ == 0`, and `Δ == 1` forces `new == 2`).
/// The genesis case carries NO `Immutable` — it must perform the `0 → 1` write itself.
fn genesis_oneshot_teeth() -> Vec<StateConstraint> {
    vec![
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
    ]
}

/// Freeze the genesis-done sentinel on a NON-genesis case: `HeapField{Immutable}` admits
/// the unchanged key (no case but genesis ever writes it) but REFUSES any write —
/// so no other method can reset the sentinel to re-open the one-shot genesis.
fn genesis_sentinel_freeze() -> StateConstraint {
    StateConstraint::HeapField {
        key: GENESIS_DONE_EXT_KEY,
        atom: HeapAtom::Immutable,
    }
}

/// **Does `program`'s genesis case carry the one-shot sentinel teeth?** — i.e. did it come
/// from [`compile_scene`], and therefore REQUIRE its genesis turn to write
/// [`GENESIS_DONE_EXT_KEY`] `0 → 1`?
///
/// The sentinel machinery keys off the INSTALLED PROGRAM, never off the method NAME.
/// Several consumers spell their own dispatch method `"genesis"` while hand-building
/// their `CompiledStory` and installing their OWN genesis case (`dregg-multiway-tug`'s
/// board, the dungeon keep, test fixtures) — those programs never mention the sentinel,
/// so [`crate::WorldCell`] must leave them BYTE-IDENTICAL to before: no sentinel born at
/// deploy, no sentinel write injected into their genesis turns, no `fields_root` moved.
/// Keying off the method string would silently write a reserved ext key into every such
/// world. So: teeth present ⇒ the world maintains the sentinel; teeth absent ⇒ untouched.
pub(crate) fn program_requires_genesis_sentinel(program: &CellProgram) -> bool {
    let CellProgram::Cases(cases) = program else {
        return false;
    };
    let genesis = symbol(GENESIS_METHOD);
    cases.iter().any(|case| {
        matches!(case.guard, TransitionGuard::MethodIs { method } if method == genesis)
            && case.constraints.iter().any(|c| {
                matches!(c, StateConstraint::HeapField { key, .. } if *key == GENESIS_DONE_EXT_KEY)
            })
    })
}

fn collect_effect(e: &Effect, vars: &mut std::collections::BTreeSet<String>) {
    match e {
        Effect::Set(s) => {
            vars.insert(s.var.to_string());
        }
        Effect::Modify(m) => {
            vars.insert(m.var.to_string());
        }
        Effect::Call(_) => {}
    }
}

fn collect_condition(
    cond: &Condition,
    vars: &mut std::collections::BTreeSet<String>,
    has: &mut std::collections::BTreeSet<(String, String)>,
) {
    collect_expr(&cond.expr, vars, has);
}

fn collect_expr(
    expr: &ConditionExpr,
    vars: &mut std::collections::BTreeSet<String>,
    has: &mut std::collections::BTreeSet<(String, String)>,
) {
    match expr {
        ConditionExpr::Atom(clause) => collect_clause(clause, vars, has),
        ConditionExpr::And(a, b) | ConditionExpr::Or(a, b) => {
            collect_expr(a, vars, has);
            collect_expr(b, vars, has);
        }
    }
}

fn collect_clause(
    clause: &ConditionClause,
    vars: &mut std::collections::BTreeSet<String>,
    has: &mut std::collections::BTreeSet<(String, String)>,
) {
    match clause {
        ConditionClause::Compare(c) => {
            vars.insert(c.var.to_string());
            // A VAR-OP-VAR gate (`{ gold >= "$price" }`): the referenced var on the
            // RHS also needs a slot so the cross-slot tooth can read it. See
            // [`var_ref`] for the `$`-sigil convention (the closest form the current
            // spween grammar expresses; a native `var op var` is the noted follow-up).
            if let Some(rname) = var_ref(&c.value) {
                vars.insert(rname.to_string());
            }
        }
        ConditionClause::Has(h) => {
            has.insert((h.category.to_string(), h.key.to_string()));
        }
        ConditionClause::Not(inner) => collect_clause(inner, vars, has),
    }
}

/// A **VAR-OP-VAR reference** on the RHS of a `Compare` clause. The current spween
/// grammar (git-pinned `emberian/spween`) parses a comparison's RHS only as a literal
/// (`parse_value` rejects a bare identifier), so `{ gold >= price }` does NOT parse.
/// The closest expressible form is a QUOTED STRING RHS, which the v0 compiler always
/// left handler-only (a string never projects to the numeric slot encoding). We give
/// that idle form a meaning: a string beginning with `$` names a VARIABLE, so
/// `{ gold >= "$price" }` is the cross-variable gate `gold >= price`. Unambiguous (a
/// real string literal does not lead with `$`) and strictly additive (a plain-string
/// RHS stays handler-only exactly as before).
///
/// FOLLOW-UP (the external grammar): teach `emberian/spween`'s `parse_condition_clause`
/// to accept an identifier RHS (`var op var`) directly, so authors can drop the
/// `"$…"` quoting; the compiler already lowers the relation, so it is a pure parser
/// widening.
fn var_ref(value: &Value) -> Option<&str> {
    match value {
        Value::String(s) => s.strip_prefix('$').filter(|r| !r.is_empty()),
        _ => None,
    }
}

/// The net delta a choice's effects apply to `var`.
fn delta_for(effects: &[Effect], var: &str) -> Delta {
    let mut sum: i64 = 0;
    for e in effects {
        match e {
            Effect::Set(s) if s.var.as_str() == var => return Delta::Overwritten,
            Effect::Modify(m) if m.var.as_str() == var => sum += m.delta,
            _ => {}
        }
    }
    Delta::Add(sum)
}

/// Lower a choice's optional gate to a `(constraints, fully_lowered)` pair. An
/// un-lowerable clause (Set-overwritten gate var, string/float compare, or nested
/// boolean beyond the v0 shapes) contributes no executor constraint and clears the
/// `fully_lowered` flag (the runtime/handler still gates it).
fn lower_gate(
    condition: Option<&Condition>,
    effects: &[Effect],
    var_slots: &BTreeMap<String, u64>,
    has_slots: &BTreeMap<(String, String), u64>,
) -> (Vec<StateConstraint>, bool) {
    let Some(cond) = condition else {
        return (vec![], true);
    };
    let mut out = Vec::new();
    let full = lower_expr(&cond.expr, effects, var_slots, has_slots, &mut out);
    (out, full)
}

/// Lower a boolean expression into the conjunction accumulator `out`. Returns
/// whether the WHOLE expression was faithfully lowered. Supported shapes: a
/// conjunction (`And`) of atoms/`Or`s/`Not`s at the top level; a single `Or` (as
/// [`StateConstraint::AnyOf`]); a `Not` of an atom. Anything else lowers what it
/// can and returns `false`.
fn lower_expr(
    expr: &ConditionExpr,
    effects: &[Effect],
    var_slots: &BTreeMap<String, u64>,
    has_slots: &BTreeMap<(String, String), u64>,
    out: &mut Vec<StateConstraint>,
) -> bool {
    match expr {
        ConditionExpr::And(a, b) => {
            let l = lower_expr(a, effects, var_slots, has_slots, out);
            let r = lower_expr(b, effects, var_slots, has_slots, out);
            l && r
        }
        ConditionExpr::Atom(clause) => match lower_clause(clause, effects, var_slots, has_slots) {
            Some(scs) => {
                out.extend(scs);
                true
            }
            None => false,
        },
        ConditionExpr::Or(a, b) => {
            // Both sides must reduce to a single simple constraint to become an AnyOf.
            match (
                simple_of_expr(a, effects, var_slots, has_slots),
                simple_of_expr(b, effects, var_slots, has_slots),
            ) {
                (Some(x), Some(y)) => {
                    out.push(StateConstraint::AnyOf {
                        variants: vec![x, y],
                    });
                    true
                }
                _ => false,
            }
        }
    }
}

/// A top-level clause → the [`StateConstraint`]s it lowers to (or `None` if
/// un-lowerable). Usually one tooth; a gate on a var the same choice DECREMENTS
/// lowers to two — the lifted comparison PLUS an exact-delta companion (see
/// [`compare_teeth`]) so the executor's clamp-at-zero cannot defeat the gate.
fn lower_clause(
    clause: &ConditionClause,
    effects: &[Effect],
    var_slots: &BTreeMap<String, u64>,
    has_slots: &BTreeMap<(String, String), u64>,
) -> Option<Vec<StateConstraint>> {
    match clause {
        ConditionClause::Compare(c) => {
            let &key = var_slots.get(c.var.as_str())?;
            let p = plane_of(key);
            // VAR-OP-VAR (`{ gold >= "$price" }`): compare two cell fields, not a field
            // to a literal. Lowers to a cross-field tooth the executor re-checks — a
            // real cross-variable gate, not a handler courtesy.
            if let Some(rname) = var_ref(&c.value) {
                let &rkey = var_slots.get(rname)?;
                return cross_var_teeth(p, plane_of(rkey), c.op, effects, c.var.as_str(), rname);
            }
            let base = numeric_value(&c.value)?;
            let d = match delta_for(effects, c.var.as_str()) {
                Delta::Add(n) => n,
                Delta::Overwritten => return None,
            };
            compare_teeth(p, c.op, base, d)
        }
        ConditionClause::Has(h) => {
            let &key = has_slots.get(&(h.category.to_string(), h.key.to_string()))?;
            // Membership: the field must read 1 in the post-state (choices do not
            // mutate membership fields in v0). On the ext plane the equality is a
            // `HeapField{Equals}`, which ALSO refuses an absent key — but a compiled
            // ext key is born at field-zero on deploy, so "absent" never arises and
            // the tooth is the exact register twin: present-and-1 admits, 0 refuses.
            Some(vec![match plane_of(key) {
                Plane::Slot(index) => StateConstraint::FieldEquals {
                    index,
                    value: field_from_u64(1),
                },
                Plane::Ext(key) => StateConstraint::HeapField {
                    key,
                    atom: HeapAtom::Equals {
                        value: field_from_u64(1),
                    },
                },
            }])
        }
        // A negated atom lowers via a single-variant AnyOf wrapping a Simple::Not.
        ConditionClause::Not(inner) => {
            let s = simple_of_clause(inner, effects, var_slots, has_slots)?;
            Some(vec![StateConstraint::AnyOf {
                variants: vec![SimpleStateConstraint::Not(Box::new(s))],
            }])
        }
    }
}

/// The teeth a numeric `var op base` (pre-state) gate lowers to, given the choice's
/// net delta `d` on that var. The lifted post-comparison (see [`compare_constraint`]),
/// PLUS — only when the executor's clamp-at-zero would DEFEAT that lift (see
/// [`lift_defeated_by_clamp`]) — a [`StateConstraint::FieldDelta`]`{ index, d }`
/// companion that PINS the delta.
///
/// The lift `pre op base ⟺ post op (base+d)` assumes `post = pre + d` exactly, but
/// the executor clamps a `Modify` at zero (`post = max(0, pre+d)`). When the shifted
/// threshold lands `≤ 0`, the clamp makes the lifted bound vacuous — e.g.
/// `{gold>=50} ~ gold-=50` shifts to `FieldGte(gold, 0)`, always true, so a broke
/// buyer's clamped-to-zero purse still passes. `FieldDelta{index, d}` requires
/// `post == old + d` in the wrapping u64 lane; a clamped underflow lands `0 ≠ old + d`
/// and is REFUSED, so the two teeth together are equivalent to the pre-gate exactly.
/// When the shifted threshold stays `> 0` the lift is already clamp-safe (a blow that
/// would underflow lands below the threshold and is caught by the comparison itself)
/// — no companion, so a case whose delta is overridden at runtime (e.g. dice combat
/// reusing an `{hp>=21} ~ hp-=20` case with a *rolled* hp delta) is not over-pinned.
/// On the EXT plane the companion is `HeapAtom::DeltaEquals { d }` — the exact-delta
/// twin of `FieldDelta`, and the SAME tooth: it requires `new[key] - old[key] == d` as
/// a signed delta with BOTH sides present, so the identical clamped underflow
/// (`{gold>=50} ~ gold-=50` on a purse of 10 landing `post = 0`, `Δ = -10 ≠ -50`) is
/// REFUSED. It is stricter than the register form in the direction that costs an
/// attacker nothing honest: an absent key refuses rather than reading zero.
fn compare_teeth(p: Plane, op: CompareOp, base: i64, d: i64) -> Option<Vec<StateConstraint>> {
    let cmp = compare_constraint(p, op, base, d)?;
    let mut teeth = vec![cmp];
    if lift_defeated_by_clamp(op, base, d) {
        teeth.push(match p {
            Plane::Slot(index) => StateConstraint::FieldDelta {
                index,
                // `d as u64` is the two's-complement additive inverse: `old + (2^64−|d|)
                // == old − |d|` mod 2^64 under the executor's wrapping `field_add`.
                delta: field_from_u64(d as u64),
            },
            // The heap atom takes the SIGNED delta directly (`field_delta_i128`), so no
            // two's-complement encoding is needed on this plane.
            Plane::Ext(key) => StateConstraint::HeapField {
                key,
                atom: HeapAtom::DeltaEquals { d },
            },
        });
    }
    Some(teeth)
}

/// Whether the executor's clamp-at-zero (`post = max(0, pre+d)`) defeats the lifted
/// post-comparison of `var op base` under net delta `d`, so the gate needs an
/// exact-delta companion (see [`compare_teeth`]).
///
/// The clamp diverges from the linear `post = pre + d` ONLY when `d < 0` (a
/// decrement can drive `pre + d` below zero). For `d ≥ 0` the lift is always exact.
/// For `d < 0` the lifted bound is defeated exactly when its shifted threshold falls
/// where `max(0, ·)` erases information (the lower-bound ops) or the clamp shrinks
/// `post` into the admitted region (the upper-bound ops):
fn lift_defeated_by_clamp(op: CompareOp, base: i64, d: i64) -> bool {
    if d >= 0 {
        return false;
    }
    match op {
        // `FieldGte{post ≥ max(0, base+d)}`: vacuous ⇔ threshold `≤ 0`.
        CompareOp::Ge => base + d <= 0,
        // `FieldGte{post ≥ max(0, base+1+d)}`: vacuous ⇔ threshold `≤ 0`.
        CompareOp::Gt => base + 1 + d <= 0,
        // `FieldEquals{post == max(0, base+d)}`: clamp region collapses to 0 ⇔ `≤ 0`.
        CompareOp::Eq => base + d <= 0,
        // Upper-bound gates on a decremented var: the clamp shrinks `post`, which can
        // over-admit a value the pre-gate would reject. Pin the delta (fail-closed);
        // no consumer gates a decremented var with `<=`/`<`.
        CompareOp::Le | CompareOp::Lt => true,
        // `!=` is not lowered (`compare_constraint` returns `None`).
        CompareOp::Ne => false,
    }
}

/// The teeth a **VAR-OP-VAR** gate (`gvar op rvar`, both variables) lowers to: a
/// cross-slot [`StateConstraint::FieldLteOther`] (`new[a] <= new[b] + delta`, signed)
/// the executor re-checks on the post-state — a real cross-variable tooth, not a
/// handler courtesy.
///
/// ## The lift (pre-gate → post-tooth), and its clamp guard
///
/// The gate is a PRE-state relation but a constraint bites POST-state. With the
/// choice's net deltas `dg` on `gvar` and `dr` on `rvar` and NO clamp, `gvar_post =
/// gvar_pre + dg` and `rvar_post = rvar_pre + dr`, so e.g. `gvar_pre >= rvar_pre ⟺
/// gvar_post >= rvar_post + (dg − dr) ⟺ new[rvar] <= new[gvar] + (dr − dg)`.
///
/// The lift assumes `post = pre + d` EXACTLY, but the executor CLAMPS a `Modify` at
/// zero (`post = max(0, pre+d)`). When BOTH deltas are non-negative (`dg ≥ 0` and
/// `dr ≥ 0`) no clamp can fire (`pre ≥ 0 ⇒ pre+d ≥ 0`) and the lift is exact, so we
/// emit the real tooth. When either operand is DECREMENTED by the same choice the
/// clamp can defeat the lift; rather than emit an under-pinned tooth we leave the whole
/// clause to the runtime/handler gate (returns `None`, clearing `fully_gated`) — the
/// cross-var clamp companion is a scheduled sharpening, and the spween grammar cannot
/// even decrement by a *variable* amount (only a literal `-=`), so a var-priced
/// purchase's gate var is untouched (`dg = 0`) in the realistic case.
///
/// `!=` has no single cross-slot `<=` form and stays handler-only (mirrors the literal
/// [`compare_constraint`] `Ne` case).
///
/// ## Across the planes
///
/// When BOTH operands are registers this is [`StateConstraint::FieldLteOther`],
/// unchanged. When EITHER spilled it is [`StateConstraint::HeapFieldLteOther`] — the
/// heap-keyed twin, whose operands are read through `CellState::get_field_ext`, which
/// resolves a key `< STATE_SLOTS` to the register file. So a MIXED pair (a register
/// `gold` against a spilled `price`) is one tooth, not a lowering gap: the same
/// `new[a] <= new[b] + delta` relation, over two keys on whichever planes they landed.
fn cross_var_teeth(
    gp: Plane,
    rp: Plane,
    op: CompareOp,
    effects: &[Effect],
    gname: &str,
    rname: &str,
) -> Option<Vec<StateConstraint>> {
    let dg = match delta_for(effects, gname) {
        Delta::Add(n) => n,
        Delta::Overwritten => return None,
    };
    let dr = match delta_for(effects, rname) {
        Delta::Add(n) => n,
        Delta::Overwritten => return None,
    };
    // Clamp guard: only the both-non-negative case lifts exactly (see doc above).
    if dg < 0 || dr < 0 {
        return None;
    }
    // `new[a] <= new[b] + delta` — the cross-REGISTER `FieldLteOther` when both
    // operands are registers (byte-identical to before), else its cross-KEY heap twin.
    let lte = |a: Plane, b: Plane, delta: i64| match (a, b) {
        (Plane::Slot(index), Plane::Slot(other)) => StateConstraint::FieldLteOther {
            index,
            other,
            delta,
        },
        _ => StateConstraint::HeapFieldLteOther {
            key: a.key(),
            other_key: b.key(),
            delta,
        },
    };
    Some(match op {
        // gvar >= rvar  ⟺  new[rvar] <= new[gvar] + (dr − dg)
        CompareOp::Ge => vec![lte(rp, gp, dr - dg)],
        // gvar <= rvar  ⟺  new[gvar] <= new[rvar] + (dg − dr)
        CompareOp::Le => vec![lte(gp, rp, dg - dr)],
        // gvar >  rvar  ⟺  gvar ≥ rvar+1  ⟺  new[rvar] <= new[gvar] + (dr − dg) − 1
        CompareOp::Gt => vec![lte(rp, gp, dr - dg - 1)],
        // gvar <  rvar  ⟺  gvar+1 ≤ rvar  ⟺  new[gvar] <= new[rvar] + (dg − dr) − 1
        CompareOp::Lt => vec![lte(gp, rp, dg - dr - 1)],
        // gvar == rvar  ⟺  the pair of `<=` bounds (each direction).
        CompareOp::Eq => vec![lte(gp, rp, dg - dr), lte(rp, gp, dr - dg)],
        // `!=` has no single cross-field `<=` form — leave to the handler gate.
        CompareOp::Ne => return None,
    })
}

/// Reduce an expression to a single [`SimpleStateConstraint`] for use inside an
/// `AnyOf` (an `Or` branch). Only atoms and negated atoms reduce; conjunction /
/// disjunction inside a branch is not supported in v0.
fn simple_of_expr(
    expr: &ConditionExpr,
    effects: &[Effect],
    var_slots: &BTreeMap<String, u64>,
    has_slots: &BTreeMap<(String, String), u64>,
) -> Option<SimpleStateConstraint> {
    match expr {
        ConditionExpr::Atom(clause) => simple_of_clause(clause, effects, var_slots, has_slots),
        _ => None,
    }
}

fn simple_of_clause(
    clause: &ConditionClause,
    effects: &[Effect],
    var_slots: &BTreeMap<String, u64>,
    has_slots: &BTreeMap<(String, String), u64>,
) -> Option<SimpleStateConstraint> {
    use SimpleStateConstraint as S;
    match clause {
        ConditionClause::Compare(c) => {
            let &key = var_slots.get(c.var.as_str())?;
            let base = numeric_value(&c.value)?;
            let d = match delta_for(effects, c.var.as_str()) {
                Delta::Add(n) => n,
                Delta::Overwritten => return None,
            };
            // When the executor's clamp would defeat the lifted comparison (see
            // `lift_defeated_by_clamp`) the gate needs an exact-delta companion — but
            // a disjunct (`AnyOf` variant) / negation cannot carry that companion, so
            // rather than emit a vacuous simple constraint we leave the whole clause
            // to the runtime/handler gate (clears `fully_gated`). No consumer gates
            // such a var behind an `Or`/`Not`; the clamp-safe shapes are unaffected.
            if lift_defeated_by_clamp(c.op, base, d) {
                return None;
            }
            simple_compare(plane_of(key), c.op, base, d)
        }
        ConditionClause::Has(h) => {
            let &key = has_slots.get(&(h.category.to_string(), h.key.to_string()))?;
            // `SimpleStateConstraint::HeapField` is the ext twin INSIDE the simple
            // fragment (same evaluator arm as the top-level `StateConstraint::HeapField`),
            // so a spilled membership atom still composes under `AnyOf` / `Not` — the
            // disjunctive/negated shapes are not a lowering gap on the wide plane.
            Some(match plane_of(key) {
                Plane::Slot(index) => S::FieldEquals {
                    index,
                    value: field_from_u64(1),
                },
                Plane::Ext(key) => S::HeapField {
                    key,
                    atom: HeapAtom::Equals {
                        value: field_from_u64(1),
                    },
                },
            })
        }
        ConditionClause::Not(inner) => {
            let s = simple_of_clause(inner, effects, var_slots, has_slots)?;
            Some(S::Not(Box::new(s)))
        }
    }
}

/// Only Int/Bool values project to the numeric slot encoding gates compare on.
fn numeric_value(v: &Value) -> Option<i64> {
    match v {
        Value::Int(n) => Some(*n),
        Value::Bool(b) => Some(*b as i64),
        _ => None,
    }
}

/// The shifted threshold a lifted comparison bounds against: `base + d`, floored at
/// zero (the field lane is unsigned). Shared by every emitter below so both planes
/// bound against the SAME number.
fn thr(t: i64) -> FieldElement {
    field_from_u64(t.max(0) as u64)
}

/// The EXT-plane twin of [`compare_constraint`]'s register arms: `var op base`
/// (pre-state) lifted to the post-state [`HeapAtom`] over the var's ext key, under the
/// choice's net delta `d`. Arm-for-arm the same lift, same shifted thresholds — the
/// only difference is which plane reads the value (`Gte`/`Lte`/`Equals` compare the
/// same big-endian 32 bytes as `FieldGte`/`FieldLte`/`FieldEquals`). This is the one
/// place the register→ext gate translation is written, so the two planes cannot drift.
fn compare_heap_atom(op: CompareOp, base: i64, d: i64) -> Option<HeapAtom> {
    Some(match op {
        // pre >= base  ⟺  post >= base + d
        CompareOp::Ge => HeapAtom::Gte {
            value: thr(base + d),
        },
        // pre >  base  ⟺  pre >= base+1  ⟺  post >= base+1+d
        CompareOp::Gt => HeapAtom::Gte {
            value: thr(base + 1 + d),
        },
        // pre <= base  ⟺  post <= base + d
        CompareOp::Le => HeapAtom::Lte {
            value: thr(base + d),
        },
        // pre <  base  ⟺  pre <= base-1  ⟺  post <= base-1+d
        CompareOp::Lt => HeapAtom::Lte {
            value: thr(base - 1 + d),
        },
        // pre == base  ⟺  post == base + d
        CompareOp::Eq => HeapAtom::Equals {
            value: thr(base + d),
        },
        // `!=` is not lowered on EITHER plane (mirrors `compare_constraint`).
        CompareOp::Ne => return None,
    })
}

/// `var op base` (pre-state) lifted to a post-state [`StateConstraint`] given the
/// choice's net delta `d` on the var (`post = pre + d`), on whichever plane the var
/// landed.
fn compare_constraint(p: Plane, op: CompareOp, base: i64, d: i64) -> Option<StateConstraint> {
    let index = match p {
        Plane::Ext(key) => {
            return Some(StateConstraint::HeapField {
                key,
                atom: compare_heap_atom(op, base, d)?,
            });
        }
        Plane::Slot(index) => index,
    };
    Some(match op {
        // pre >= base  ⟺  post >= base + d
        CompareOp::Ge => StateConstraint::FieldGte {
            index,
            value: thr(base + d),
        },
        // pre >  base  ⟺  pre >= base+1  ⟺  post >= base+1+d
        CompareOp::Gt => StateConstraint::FieldGte {
            index,
            value: thr(base + 1 + d),
        },
        // pre <= base  ⟺  post <= base + d
        CompareOp::Le => StateConstraint::FieldLte {
            index,
            value: thr(base + d),
        },
        // pre <  base  ⟺  pre <= base-1  ⟺  post <= base-1+d
        CompareOp::Lt => StateConstraint::FieldLte {
            index,
            value: thr(base - 1 + d),
        },
        // pre == base  ⟺  post == base + d
        CompareOp::Eq => StateConstraint::FieldEquals {
            index,
            value: thr(base + d),
        },
        // `!=` has no single-atom post-state form here — leave to the handler gate.
        CompareOp::Ne => return None,
    })
}

fn simple_compare(p: Plane, op: CompareOp, base: i64, d: i64) -> Option<SimpleStateConstraint> {
    use SimpleStateConstraint as S;
    let index = match p {
        Plane::Ext(key) => {
            return Some(S::HeapField {
                key,
                atom: compare_heap_atom(op, base, d)?,
            });
        }
        Plane::Slot(index) => index,
    };
    Some(match op {
        CompareOp::Ge => S::FieldGte {
            index,
            value: thr(base + d),
        },
        CompareOp::Gt => S::FieldGte {
            index,
            value: thr(base + 1 + d),
        },
        CompareOp::Le => S::FieldLte {
            index,
            value: thr(base + d),
        },
        CompareOp::Lt => S::FieldLte {
            index,
            value: thr(base - 1 + d),
        },
        CompareOp::Eq => S::FieldEquals {
            index,
            value: thr(base + d),
        },
        CompareOp::Ne => return None,
    })
}

/// Encode a [`Value`] as the cell's numeric field projection (the representation
/// the executor gate compares against). Re-exported convenience.
pub fn value_to_field(v: &Value) -> FieldElement {
    field_from_u64(value_to_u64(v))
}
