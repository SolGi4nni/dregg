//! The Q1 query surface: conjunctive queries over the EDB — patterns,
//! filters, joins on shared variables, and (safe, EDB-only) negated atoms.
//!
//! Deliberately NOT a Datalog engine (the trap docs/EPISTEMIC-DATALOG.md
//! names): no user-defined IDB rules, no recursion, no stratification
//! machinery. A query is one conjunction. Negated atoms exist because
//! "granted and not revoked" is the canonical query — and because they are
//! exactly what the CALM classifier ([`crate::classify`]) needs to grade.
//!
//! Evaluation is a nested-loop join with binding propagation — fine for the
//! receipt-slice cardinalities this crate serves (a certified range of a
//! node's receipt chain), and small enough to audit.

use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use thiserror::Error;

use crate::fact::{FactBase, Pred, Value};

/// A term in a query atom: a variable, the anonymous wildcard `_`, or a
/// ground constant.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum Term {
    /// A named variable — joins on name across atoms.
    Var(String),
    /// The anonymous wildcard: matches anything, binds nothing.
    Wild,
    /// A ground constant.
    Const(Value),
}

impl Term {
    pub fn var(s: impl Into<String>) -> Self {
        Term::Var(s.into())
    }
    pub fn sym(s: impl Into<String>) -> Self {
        Term::Const(Value::sym(s))
    }
    pub fn nat(n: u64) -> Self {
        Term::Const(Value::nat(n))
    }
}

/// One pattern atom: a predicate applied to terms. Arity is checked at eval.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Atom {
    pub pred: Pred,
    pub args: Vec<Term>,
}

impl Atom {
    pub fn new(pred: Pred, args: Vec<Term>) -> Self {
        Atom { pred, args }
    }
}

/// Comparison operators for filters. Ordered comparisons are defined on
/// `Nat`-`Nat` pairs only; a type-mismatched ordered comparison is FALSE
/// (fail closed). `Eq`/`Ne` compare any two values.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CmpOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

/// A filter over bound terms: `lhs op rhs`, e.g. `A > 100`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Filter {
    pub lhs: Term,
    pub op: CmpOp,
    pub rhs: Term,
}

/// An aggregation operator (the Q3 surface, toward
/// docs/EPISTEMIC-DATALOG.md). All four are NON-MONOTONE in their value over an
/// append-only EDB — `count`/`sum` grow, `min` falls, `max` rises as more
/// receipts arrive — so any query that aggregates is graded
/// [`crate::classify::CoordinationClass::FinalizedDependent`]: the aggregate is
/// exact only for the certified, finalized prefix.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum AggOp {
    /// Count of distinct answer rows in the group. (`arg` is ignored / `None`.)
    Count,
    /// Sum of the `Nat` values bound to `arg` across the group.
    Sum,
    /// Minimum of the `Nat` values bound to `arg`.
    Min,
    /// Maximum of the `Nat` values bound to `arg`.
    Max,
}

/// One aggregate term: `op(arg) AS as_name`. For [`AggOp::Count`] `arg` is
/// `None` (count of rows); for `Sum`/`Min`/`Max` it names the positively-bound
/// variable whose `Nat` values are folded. `as_name` is a FRESH output column —
/// it must not collide with any positive/group variable.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Aggregate {
    pub op: AggOp,
    pub arg: Option<String>,
    pub as_name: String,
}

/// A conjunctive query: positive atoms (joined on shared variables), negated
/// atoms (safe: every named variable in a negated atom must occur in some
/// positive atom), filters (every named variable must be positively bound),
/// and an optional aggregation layer (`group_by` + `aggregates`) applied to the
/// deduplicated answer set.
///
/// When `aggregates` is non-empty the output rows bind exactly the `group_by`
/// variables plus the aggregates' `as_name`s (the other positive variables are
/// projected away). `group_by` with empty `aggregates` is a DISTINCT projection
/// onto those variables — still monotone. `group_by` empty with aggregates is a
/// single global-aggregate row.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Query {
    pub atoms: Vec<Atom>,
    pub negated: Vec<Atom>,
    pub filters: Vec<Filter>,
    #[serde(default)]
    pub group_by: Vec<String>,
    #[serde(default)]
    pub aggregates: Vec<Aggregate>,
}

impl Query {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn atom(mut self, pred: Pred, args: Vec<Term>) -> Self {
        self.atoms.push(Atom::new(pred, args));
        self
    }
    pub fn not_atom(mut self, pred: Pred, args: Vec<Term>) -> Self {
        self.negated.push(Atom::new(pred, args));
        self
    }
    pub fn filter(mut self, lhs: Term, op: CmpOp, rhs: Term) -> Self {
        self.filters.push(Filter { lhs, op, rhs });
        self
    }
    /// Group the answer set by these variables (in order). Each must be a
    /// positively-bound variable.
    pub fn group_by(mut self, vars: impl IntoIterator<Item = impl Into<String>>) -> Self {
        self.group_by = vars.into_iter().map(Into::into).collect();
        self
    }
    /// Add an aggregate `op(arg) AS as_name`.
    pub fn aggregate(
        mut self,
        op: AggOp,
        arg: Option<impl Into<String>>,
        as_name: impl Into<String>,
    ) -> Self {
        self.aggregates.push(Aggregate {
            op,
            arg: arg.map(Into::into),
            as_name: as_name.into(),
        });
        self
    }

    /// All named variables of a term slice.
    fn vars_of(args: &[Term]) -> impl Iterator<Item = &str> {
        args.iter().filter_map(|t| match t {
            Term::Var(v) => Some(v.as_str()),
            _ => None,
        })
    }
}

/// One answer row: variable name → ground value.
pub type Bindings = BTreeMap<String, Value>;

#[derive(Debug, Error, PartialEq, Eq)]
pub enum QueryError {
    #[error("atom {pred:?} has {got} args, schema arity is {want}")]
    Arity { pred: Pred, got: usize, want: usize },
    #[error("unsafe variable {0:?}: occurs in a negated atom or filter but in no positive atom")]
    Unsafe(String),
    #[error("query has no positive atoms")]
    Empty,
    #[error("aggregate {op:?} requires an argument variable")]
    AggMissingArg { op: AggOp },
    #[error("aggregate output column {0:?} collides with a query/group variable")]
    AggCollision(String),
    #[error("aggregate {op:?} over {var:?}: value {value} is not a number")]
    AggType {
        op: AggOp,
        var: String,
        value: Value,
    },
}

/// Validate arities + safety (range-restriction): every named variable used
/// in a negated atom or filter must occur in a positive atom.
pub fn validate(q: &Query) -> Result<(), QueryError> {
    if q.atoms.is_empty() {
        return Err(QueryError::Empty);
    }
    for a in q.atoms.iter().chain(q.negated.iter()) {
        if a.args.len() != a.pred.arity() {
            return Err(QueryError::Arity {
                pred: a.pred,
                got: a.args.len(),
                want: a.pred.arity(),
            });
        }
    }
    let positive: BTreeSet<&str> = q
        .atoms
        .iter()
        .flat_map(|a| Query::vars_of(&a.args))
        .collect();
    for a in &q.negated {
        for v in Query::vars_of(&a.args) {
            if !positive.contains(v) {
                return Err(QueryError::Unsafe(v.to_string()));
            }
        }
    }
    for f in &q.filters {
        for t in [&f.lhs, &f.rhs] {
            if let Term::Var(v) = t
                && !positive.contains(v.as_str())
            {
                return Err(QueryError::Unsafe(v.clone()));
            }
        }
    }
    // Aggregation safety: group-by and aggregate-argument variables must be
    // positively bound; aggregate output columns must be fresh names (not a
    // positive or group variable, nor another aggregate's column).
    for v in &q.group_by {
        if !positive.contains(v.as_str()) {
            return Err(QueryError::Unsafe(v.clone()));
        }
    }
    let mut out_names: BTreeSet<&str> = BTreeSet::new();
    for agg in &q.aggregates {
        match agg.op {
            AggOp::Count => {}
            AggOp::Sum | AggOp::Min | AggOp::Max => {
                let Some(arg) = &agg.arg else {
                    return Err(QueryError::AggMissingArg { op: agg.op });
                };
                if !positive.contains(arg.as_str()) {
                    return Err(QueryError::Unsafe(arg.clone()));
                }
            }
        }
        if positive.contains(agg.as_name.as_str())
            || q.group_by.iter().any(|g| g == &agg.as_name)
            || !out_names.insert(agg.as_name.as_str())
        {
            return Err(QueryError::AggCollision(agg.as_name.clone()));
        }
    }
    Ok(())
}

/// Try to extend `binding` so that `atom` matches `fact` — unification of a
/// pattern against a ground fact.
///
/// The input `binding` is only cloned on a CONFIRMED match: const positions and
/// already-bound (or repeated-within-atom) variable positions are checked first
/// against `binding` directly; only once every position agrees is `binding`
/// cloned and the newly-bound variables inserted. A mismatch returns `None`
/// without having allocated.
fn unify(atom: &Atom, fact_args: &[Value], binding: &Bindings) -> Option<Bindings> {
    // Variables this atom newly binds (name → value), in order. A variable that
    // recurs within the same atom is checked against the value its first
    // occurrence pinned.
    let mut pending: Vec<(&str, &Value)> = Vec::new();
    for (t, v) in atom.args.iter().zip(fact_args.iter()) {
        match t {
            Term::Wild => {}
            Term::Const(c) => {
                if c != v {
                    return None;
                }
            }
            Term::Var(name) => {
                if let Some(bound) = binding.get(name) {
                    if bound != v {
                        return None;
                    }
                } else if let Some((_, pinned)) = pending.iter().find(|(n, _)| *n == name) {
                    if *pinned != v {
                        return None;
                    }
                } else {
                    pending.push((name, v));
                }
            }
        }
    }
    // Confirmed match: clone once and apply the new bindings.
    let mut b = binding.clone();
    for (name, v) in pending {
        b.insert(name.to_string(), v.clone());
    }
    Some(b)
}

/// Does `atom`, with `binding` applied, match ANY fact in the base?
/// (The negated-atom check; unbound named vars — excluded by safety — and
/// wildcards act existentially.)
fn matches_some(base: &FactBase, atom: &Atom, binding: &Bindings) -> bool {
    base.with_pred(atom.pred)
        .any(|f| unify(atom, &f.args, binding).is_some())
}

fn resolve<'a>(t: &'a Term, b: &'a Bindings) -> Option<&'a Value> {
    match t {
        Term::Const(c) => Some(c),
        Term::Var(v) => b.get(v),
        Term::Wild => None,
    }
}

fn filter_holds(f: &Filter, b: &Bindings) -> bool {
    let (Some(l), Some(r)) = (resolve(&f.lhs, b), resolve(&f.rhs, b)) else {
        return false; // unresolvable (wildcard in a filter) — fail closed
    };
    match f.op {
        CmpOp::Eq => l == r,
        CmpOp::Ne => l != r,
        // Ordered comparisons: Nat-Nat only; mismatched types are FALSE.
        CmpOp::Lt | CmpOp::Le | CmpOp::Gt | CmpOp::Ge => match (l, r) {
            (Value::Nat(a), Value::Nat(c)) => match f.op {
                CmpOp::Lt => a < c,
                CmpOp::Le => a <= c,
                CmpOp::Gt => a > c,
                CmpOp::Ge => a >= c,
                _ => unreachable!(),
            },
            _ => false,
        },
    }
}

/// Evaluate a conjunctive query against the fact base. Returns the
/// deduplicated answer rows (each row binds exactly the query's named
/// variables that occur in positive atoms).
pub fn eval(base: &FactBase, q: &Query) -> Result<Vec<Bindings>, QueryError> {
    validate(q)?;
    // Hash-join with binding propagation. Each atom is joined against a per-atom
    // index over the base facts of its predicate, keyed by the values at its
    // "join positions" — the positions whose term is either a constant or a
    // variable already bound by a previous atom. Those values are fully
    // determined by the incoming row, so the matching facts can be looked up
    // directly instead of scanning every fact of the predicate. Non-join
    // positions (wildcards, fresh variables) are resolved by `unify` exactly as
    // before, so the answer set is identical to the nested-loop join.
    let mut rows: Vec<Bindings> = vec![Bindings::new()];
    // Variables bound so far (after each atom). Determines which positions of the
    // NEXT atom are join positions.
    let mut bound: BTreeSet<&str> = BTreeSet::new();
    for atom in &q.atoms {
        let join_positions = join_positions(atom, &bound);
        let index = build_join_index(base, atom, &join_positions);

        let mut next = Vec::new();
        for b in &rows {
            // The probe key is the required values at the join positions. `Some(key)`
            // → look the matching facts up directly in the index; `None` (a wildcard in
            // a join position resolved to no value) → fall back to scanning every fact
            // of the predicate, exactly as the nested-loop join would (so the answer set
            // is identical). `unify` does the final per-position match in both arms.
            let scanned: Vec<&crate::fact::Fact>;
            let candidates: &[&crate::fact::Fact] = match probe_key(atom, &join_positions, b) {
                Some(key) => index.get(&key).map(Vec::as_slice).unwrap_or(&[]),
                None => {
                    scanned = base.with_pred(atom.pred).collect();
                    &scanned
                }
            };
            for f in candidates {
                if let Some(b2) = unify(atom, &f.args, b) {
                    next.push(b2);
                }
            }
        }
        rows = next;
        if rows.is_empty() {
            return Ok(vec![]);
        }
        // Every named variable of this atom is now bound.
        for v in Query::vars_of(&atom.args) {
            bound.insert(v);
        }
    }
    // Negated atoms: keep rows where the negated pattern matches NOTHING.
    // Each negated atom is, by safety (range-restriction), fully bound by the
    // positive atoms, so all of its named-variable positions are join positions
    // and it can be checked against an anti-join index instead of re-scanning
    // the base per surviving row.
    if !q.negated.is_empty() {
        let neg_indexes: Vec<(&Atom, Vec<usize>, std::collections::HashMap<Vec<Value>, ()>)> = q
            .negated
            .iter()
            .map(|a| {
                let positions = join_positions(a, &bound);
                let mut idx: std::collections::HashMap<Vec<Value>, ()> =
                    std::collections::HashMap::new();
                for f in base.with_pred(a.pred) {
                    idx.entry(positions.iter().map(|&p| f.args[p].clone()).collect())
                        .or_insert(());
                }
                (a, positions, idx)
            })
            .collect();
        rows.retain(|b| {
            neg_indexes.iter().all(|(a, positions, idx)| {
                let key = probe_key(a, positions, b);
                // A wildcard / unbound position (probe_key None) means the
                // negated pattern matches existentially — fall back to the
                // scan-based check for that atom. Safety guarantees named vars
                // are bound, so this only triggers for wildcards.
                match key {
                    Some(k) => !idx.contains_key(&k),
                    None => !matches_some(base, a, b),
                }
            })
        });
    }
    // Filters.
    rows.retain(|b| q.filters.iter().all(|f| filter_holds(f, b)));
    // Deduplicate (set semantics) — the conjunctive answer set.
    let set: BTreeSet<Bindings> = rows.into_iter().collect();
    // Aggregation / projection layer, if requested.
    if q.group_by.is_empty() && q.aggregates.is_empty() {
        return Ok(set.into_iter().collect());
    }
    aggregate(&set, q)
}

/// The Q3 group-by + aggregate fold over the deduplicated answer set. Groups
/// are keyed by the `group_by` tuple (empty group-by ⇒ one global group, but
/// only when there are aggregates — a group-by-only query with NO rows yields
/// no groups). Output rows bind the group variables plus each aggregate's
/// `as_name`. Output is already group-distinct, so no further dedup is needed.
fn aggregate(set: &BTreeSet<Bindings>, q: &Query) -> Result<Vec<Bindings>, QueryError> {
    // Group key → member rows. A BTreeMap keeps groups in a deterministic order.
    let mut groups: BTreeMap<Vec<Value>, Vec<&Bindings>> = BTreeMap::new();
    for row in set {
        let key: Vec<Value> = q
            .group_by
            .iter()
            .map(|g| row.get(g).cloned().unwrap_or(Value::Nat(0)))
            .collect();
        groups.entry(key).or_default().push(row);
    }
    // A global aggregate (no group-by) over an EMPTY set still yields one row
    // (count = 0); a grouped query over an empty set yields no rows.
    if groups.is_empty() && q.group_by.is_empty() && !q.aggregates.is_empty() {
        groups.insert(Vec::new(), Vec::new());
    }
    let mut out = Vec::with_capacity(groups.len());
    for (key, members) in groups {
        let mut b = Bindings::new();
        for (g, v) in q.group_by.iter().zip(key) {
            b.insert(g.clone(), v);
        }
        for agg in &q.aggregates {
            b.insert(agg.as_name.clone(), fold_agg(agg, &members)?);
        }
        out.push(b);
    }
    Ok(out)
}

/// Fold one aggregate over a group's member rows. `Sum`/`Min`/`Max` require
/// every contributing value to be a `Nat` (the EDB's amounts/heights are); a
/// `Sym` in a numeric aggregate fails closed with [`QueryError::AggType`].
fn fold_agg(agg: &Aggregate, members: &[&Bindings]) -> Result<Value, QueryError> {
    if agg.op == AggOp::Count {
        return Ok(Value::Nat(members.len() as u64));
    }
    let arg = agg.arg.as_ref().expect("validated: numeric agg has an arg");
    let nat = |b: &Bindings| -> Result<u64, QueryError> {
        match b.get(arg) {
            Some(Value::Nat(n)) => Ok(*n),
            other => Err(QueryError::AggType {
                op: agg.op,
                var: arg.clone(),
                value: other.cloned().unwrap_or(Value::Nat(0)),
            }),
        }
    };
    let mut iter = members.iter();
    let first = match iter.next() {
        Some(b) => nat(b)?,
        // Empty numeric group (only reachable for a global Sum over no rows).
        None => return Ok(Value::Nat(0)),
    };
    let mut acc = first;
    for b in iter {
        let n = nat(b)?;
        acc = match agg.op {
            AggOp::Sum => acc.saturating_add(n),
            AggOp::Min => acc.min(n),
            AggOp::Max => acc.max(n),
            AggOp::Count => unreachable!(),
        };
    }
    Ok(Value::Nat(acc))
}

/// The "join positions" of an atom given the set of already-bound variables:
/// argument positions whose term is a constant or an already-bound variable —
/// i.e. positions whose required value is fully determined by the incoming row.
fn join_positions(atom: &Atom, bound: &BTreeSet<&str>) -> Vec<usize> {
    atom.args
        .iter()
        .enumerate()
        .filter_map(|(i, t)| match t {
            Term::Const(_) => Some(i),
            Term::Var(v) if bound.contains(v.as_str()) => Some(i),
            _ => None,
        })
        .collect()
}

/// Build an index over `base`'s facts of `atom.pred`, keyed by the tuple of
/// values at `join_positions`. A fact whose join-position values match a probe
/// key is a join candidate (the const / bound-var positions already agree;
/// `unify` resolves the rest). Insertion order within a bucket is preserved so
/// the produced rows match the nested-loop order before dedup.
fn build_join_index<'a>(
    base: &'a FactBase,
    atom: &Atom,
    join_positions: &[usize],
) -> std::collections::HashMap<Vec<Value>, Vec<&'a crate::fact::Fact>> {
    let mut index: std::collections::HashMap<Vec<Value>, Vec<&'a crate::fact::Fact>> =
        std::collections::HashMap::new();
    for f in base.with_pred(atom.pred) {
        let key: Vec<Value> = join_positions.iter().map(|&p| f.args[p].clone()).collect();
        index.entry(key).or_default().push(f);
    }
    index
}

/// The probe key of an atom for a given binding: the required values at its join
/// positions. Returns `None` if any join position resolves to an unbound value
/// (only possible for a wildcard, never for a const or — by construction — a
/// bound var), signaling the caller to fall back to a scan.
fn probe_key(atom: &Atom, join_positions: &[usize], b: &Bindings) -> Option<Vec<Value>> {
    join_positions
        .iter()
        .map(|&p| match &atom.args[p] {
            Term::Const(c) => Some(c.clone()),
            Term::Var(v) => b.get(v).cloned(),
            Term::Wild => None,
        })
        .collect()
}
