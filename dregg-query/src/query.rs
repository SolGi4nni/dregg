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

/// A conjunctive query: positive atoms (joined on shared variables), negated
/// atoms (safe: every named variable in a negated atom must occur in some
/// positive atom), and filters (every named variable must be positively
/// bound).
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Query {
    pub atoms: Vec<Atom>,
    pub negated: Vec<Atom>,
    pub filters: Vec<Filter>,
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
    Ok(())
}

/// Try to extend `binding` so that `atom` matches `fact` — unification of a
/// pattern against a ground fact.
fn unify(atom: &Atom, fact_args: &[Value], binding: &Bindings) -> Option<Bindings> {
    let mut b = binding.clone();
    for (t, v) in atom.args.iter().zip(fact_args.iter()) {
        match t {
            Term::Wild => {}
            Term::Const(c) => {
                if c != v {
                    return None;
                }
            }
            Term::Var(name) => match b.get(name) {
                Some(bound) => {
                    if bound != v {
                        return None;
                    }
                }
                None => {
                    b.insert(name.clone(), v.clone());
                }
            },
        }
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
    // Nested-loop join with binding propagation.
    let mut rows: Vec<Bindings> = vec![Bindings::new()];
    for atom in &q.atoms {
        let mut next = Vec::new();
        for b in &rows {
            for f in base.with_pred(atom.pred) {
                if let Some(b2) = unify(atom, &f.args, b) {
                    next.push(b2);
                }
            }
        }
        rows = next;
        if rows.is_empty() {
            return Ok(vec![]);
        }
    }
    // Negated atoms: keep rows where the negated pattern matches NOTHING.
    rows.retain(|b| q.negated.iter().all(|a| !matches_some(base, a, b)));
    // Filters.
    rows.retain(|b| q.filters.iter().all(|f| filter_holds(f, b)));
    // Deduplicate (set semantics).
    let set: BTreeSet<Bindings> = rows.into_iter().collect();
    Ok(set.into_iter().collect())
}
