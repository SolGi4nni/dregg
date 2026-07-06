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
//! ## The slot layout
//!
//! * slot [`PASSAGE_SLOT`] (0): the current passage index (the `RuntimeState`
//!   control-flow position, made cell state). [`PASSAGE_ENDED`] marks a finished
//!   scene.
//! * slots `1..`: one per numeric/bool variable named in a condition or effect,
//!   then one per `category.key` membership atom. Assignment is deterministic
//!   (sorted names) so a re-compile of the same scene yields the same layout.
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
//! against a string/float is likewise handler-only in v0. The numeric/bool gates
//! (`courage >= 5`, `gold >= 100`, `inventory.key`) lower to real executor teeth.

use std::collections::BTreeMap;

use dregg_app_framework::{
    CellProgram, FieldElement, StateConstraint, TransitionCase, TransitionGuard, field_from_u64,
    symbol,
};
use dregg_cell::program::SimpleStateConstraint;
use spween::{
    CompareOp, Condition, ConditionClause, ConditionExpr, Effect, PassageContent, Scene, Value,
};

use crate::encoding::value_to_u64;

/// The cell slot holding the current passage index (the story's program counter).
pub const PASSAGE_SLOT: usize = 0;

/// Sentinel value stored in [`PASSAGE_SLOT`] when the scene has ended (`-> END` or
/// a choice with no navigation target). Distinct from any real passage index.
pub const PASSAGE_ENDED: u64 = 0xFFFF_FFFF;

/// The number of cell state slots available (mirrors `dregg_cell::state::STATE_SLOTS`).
const STATE_SLOTS: usize = 16;

/// The dispatch method a choice's turn presents — the key its executor-enforced
/// gate case is guarded by. Used by BOTH the compiler (to name the case) and the
/// driver (to name the action), so they always agree.
pub fn choice_method(passage: &str, choice_index: usize) -> String {
    format!("c/{passage}/{choice_index}")
}

/// The dispatch method the genesis turn (the intro passage's entry effects +
/// initial passage-slot bind) presents.
pub const GENESIS_METHOD: &str = "genesis";

/// A story lowered to a world-cell descriptor: the slot layout, the passage index,
/// and the installed [`CellProgram`].
#[derive(Clone, Debug)]
pub struct CompiledStory {
    /// The scene id (drives the deterministic world-cell identity).
    pub scene_id: String,
    /// Variable name → cell slot (numeric/bool projection). Every variable named
    /// in a condition or a Set/Modify effect gets a slot.
    pub var_slots: BTreeMap<String, usize>,
    /// `(category, key)` membership atom → cell slot (1 = present, 0 = absent).
    pub has_slots: BTreeMap<(String, String), usize>,
    /// Passage name → index (matches `spween::Runtime`'s enumerate order).
    pub passage_index: BTreeMap<String, usize>,
    /// The installed program: one method-guarded case per choice + a genesis case.
    pub program: CellProgram,
    /// Per gated choice, whether the gate lowered FULLY to executor constraints
    /// (`true`) or leans on the runtime/handler for some clause (`false`). Keyed by
    /// the choice method. Absent ⇒ the choice is ungated.
    pub fully_gated: BTreeMap<String, bool>,
}

/// Why a scene could not be compiled to a world-cell.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CompileError {
    /// The scene needs more variable/membership slots than the cell has.
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

    // Deterministic slot assignment: passage slot 0, then vars, then membership.
    let mut var_slots = BTreeMap::new();
    let mut has_slots = BTreeMap::new();
    let mut next = PASSAGE_SLOT + 1;
    let total = var_names.len() + has_atoms.len();
    if next + total > STATE_SLOTS {
        return Err(CompileError::TooManySlots {
            needed: next + total,
            available: STATE_SLOTS,
        });
    }
    for name in &var_names {
        var_slots.insert(name.clone(), next);
        next += 1;
    }
    for atom in &has_atoms {
        has_slots.insert(atom.clone(), next);
        next += 1;
    }

    // One method-guarded case per choice (default-deny requires every choice-turn's
    // method to match a case), plus a permissive genesis case.
    let mut cases = vec![TransitionCase {
        guard: TransitionGuard::MethodIs {
            method: symbol(GENESIS_METHOD),
        },
        constraints: vec![],
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
            let (constraints, full) = lower_gate(
                choice.condition.as_ref(),
                &choice.effects,
                &var_slots,
                &has_slots,
            );
            if choice.condition.is_some() {
                fully_gated.insert(method.clone(), full);
            }
            cases.push(TransitionCase {
                guard: TransitionGuard::MethodIs {
                    method: symbol(&method),
                },
                constraints,
            });
            choice_idx += 1;
        }
    }

    Ok(CompiledStory {
        scene_id: scene.meta.id.to_string(),
        var_slots,
        has_slots,
        passage_index,
        program: CellProgram::Cases(cases),
        fully_gated,
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
        }
        ConditionClause::Has(h) => {
            has.insert((h.category.to_string(), h.key.to_string()));
        }
        ConditionClause::Not(inner) => collect_clause(inner, vars, has),
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
    var_slots: &BTreeMap<String, usize>,
    has_slots: &BTreeMap<(String, String), usize>,
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
    var_slots: &BTreeMap<String, usize>,
    has_slots: &BTreeMap<(String, String), usize>,
    out: &mut Vec<StateConstraint>,
) -> bool {
    match expr {
        ConditionExpr::And(a, b) => {
            let l = lower_expr(a, effects, var_slots, has_slots, out);
            let r = lower_expr(b, effects, var_slots, has_slots, out);
            l && r
        }
        ConditionExpr::Atom(clause) => match lower_clause(clause, effects, var_slots, has_slots) {
            Some(sc) => {
                out.push(sc);
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

/// A top-level clause → one [`StateConstraint`] (or `None` if un-lowerable).
fn lower_clause(
    clause: &ConditionClause,
    effects: &[Effect],
    var_slots: &BTreeMap<String, usize>,
    has_slots: &BTreeMap<(String, String), usize>,
) -> Option<StateConstraint> {
    match clause {
        ConditionClause::Compare(c) => {
            let &slot = var_slots.get(c.var.as_str())?;
            let base = numeric_value(&c.value)?;
            let d = match delta_for(effects, c.var.as_str()) {
                Delta::Add(n) => n,
                Delta::Overwritten => return None,
            };
            compare_constraint(slot as u8, c.op, base, d)
        }
        ConditionClause::Has(h) => {
            let &slot = has_slots.get(&(h.category.to_string(), h.key.to_string()))?;
            // Membership: the slot must read 1 in the post-state (choices do not
            // mutate membership slots in v0).
            Some(StateConstraint::FieldEquals {
                index: slot as u8,
                value: field_from_u64(1),
            })
        }
        // A negated atom lowers via a single-variant AnyOf wrapping a Simple::Not.
        ConditionClause::Not(inner) => {
            let s = simple_of_clause(inner, effects, var_slots, has_slots)?;
            Some(StateConstraint::AnyOf {
                variants: vec![SimpleStateConstraint::Not(Box::new(s))],
            })
        }
    }
}

/// Reduce an expression to a single [`SimpleStateConstraint`] for use inside an
/// `AnyOf` (an `Or` branch). Only atoms and negated atoms reduce; conjunction /
/// disjunction inside a branch is not supported in v0.
fn simple_of_expr(
    expr: &ConditionExpr,
    effects: &[Effect],
    var_slots: &BTreeMap<String, usize>,
    has_slots: &BTreeMap<(String, String), usize>,
) -> Option<SimpleStateConstraint> {
    match expr {
        ConditionExpr::Atom(clause) => simple_of_clause(clause, effects, var_slots, has_slots),
        _ => None,
    }
}

fn simple_of_clause(
    clause: &ConditionClause,
    effects: &[Effect],
    var_slots: &BTreeMap<String, usize>,
    has_slots: &BTreeMap<(String, String), usize>,
) -> Option<SimpleStateConstraint> {
    use SimpleStateConstraint as S;
    match clause {
        ConditionClause::Compare(c) => {
            let &slot = var_slots.get(c.var.as_str())?;
            let base = numeric_value(&c.value)?;
            let d = match delta_for(effects, c.var.as_str()) {
                Delta::Add(n) => n,
                Delta::Overwritten => return None,
            };
            simple_compare(slot as u8, c.op, base, d)
        }
        ConditionClause::Has(h) => {
            let &slot = has_slots.get(&(h.category.to_string(), h.key.to_string()))?;
            Some(S::FieldEquals {
                index: slot as u8,
                value: field_from_u64(1),
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

/// `var op base` (pre-state) lifted to a post-state [`StateConstraint`] given the
/// choice's net delta `d` on the var (`post = pre + d`).
fn compare_constraint(slot: u8, op: CompareOp, base: i64, d: i64) -> Option<StateConstraint> {
    let thr = |t: i64| field_from_u64(t.max(0) as u64);
    Some(match op {
        // pre >= base  ⟺  post >= base + d
        CompareOp::Ge => StateConstraint::FieldGte {
            index: slot,
            value: thr(base + d),
        },
        // pre >  base  ⟺  pre >= base+1  ⟺  post >= base+1+d
        CompareOp::Gt => StateConstraint::FieldGte {
            index: slot,
            value: thr(base + 1 + d),
        },
        // pre <= base  ⟺  post <= base + d
        CompareOp::Le => StateConstraint::FieldLte {
            index: slot,
            value: thr(base + d),
        },
        // pre <  base  ⟺  pre <= base-1  ⟺  post <= base-1+d
        CompareOp::Lt => StateConstraint::FieldLte {
            index: slot,
            value: thr(base - 1 + d),
        },
        // pre == base  ⟺  post == base + d
        CompareOp::Eq => StateConstraint::FieldEquals {
            index: slot,
            value: thr(base + d),
        },
        // `!=` has no single-atom post-state form here — leave to the handler gate.
        CompareOp::Ne => return None,
    })
}

fn simple_compare(slot: u8, op: CompareOp, base: i64, d: i64) -> Option<SimpleStateConstraint> {
    use SimpleStateConstraint as S;
    let thr = |t: i64| field_from_u64(t.max(0) as u64);
    Some(match op {
        CompareOp::Ge => S::FieldGte {
            index: slot,
            value: thr(base + d),
        },
        CompareOp::Gt => S::FieldGte {
            index: slot,
            value: thr(base + 1 + d),
        },
        CompareOp::Le => S::FieldLte {
            index: slot,
            value: thr(base + d),
        },
        CompareOp::Lt => S::FieldLte {
            index: slot,
            value: thr(base - 1 + d),
        },
        CompareOp::Eq => S::FieldEquals {
            index: slot,
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
