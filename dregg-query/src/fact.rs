//! The ground-fact schema — the EDB of docs/EPISTEMIC-DATALOG.md.
//!
//! Ground predicates extracted from the receipt graph + cell state:
//!
//! - `created(Agent, Cell, Height)`
//! - `transfer(From, To, Asset, Amount, Height)`
//! - `balance(Cell, Asset, Amount, Height)`
//! - `granted(From, To, Cap, Height)`
//! - `revoked(Cap, Height)`
//!
//! Every predicate is HEIGHT-STAMPED in its last argument and the fact base
//! is append-only — monotone by construction. A `balance` fact is a stamped
//! *observation* ("at height H the balance was A"), not a mutable register:
//! that is what keeps the EDB monotone while the underlying resource layer is
//! linear (the FACT/FICTION line of the doc).

use serde::{Deserialize, Serialize};
use std::fmt;

/// Block height (the monotone stamp on every fact).
pub type Height = u64;

/// A ground term. `Sym` carries identities (agent/cell/cap/asset ids — hex
/// strings on the node wire); `Nat` carries amounts and heights.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(untagged)]
pub enum Value {
    Nat(u64),
    Sym(String),
}

impl Value {
    pub fn sym(s: impl Into<String>) -> Self {
        Value::Sym(s.into())
    }
    pub fn nat(n: u64) -> Self {
        Value::Nat(n)
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Nat(n) => write!(f, "{n}"),
            Value::Sym(s) => write!(f, "{s}"),
        }
    }
}

/// The EDB predicate names. Closed set — the Q1 schema, NOT extensible
/// user-defined IDB rules (the full-Datalog trap the staging doc names).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Pred {
    Created,
    Transfer,
    Balance,
    Granted,
    Revoked,
}

impl Pred {
    /// Argument count, height stamp included (always the LAST argument).
    pub fn arity(self) -> usize {
        match self {
            Pred::Created => 3,
            Pred::Transfer => 5,
            Pred::Balance => 4,
            Pred::Granted => 4,
            Pred::Revoked => 2,
        }
    }

    /// The schema's field names, for display / row labeling.
    pub fn field_names(self) -> &'static [&'static str] {
        match self {
            Pred::Created => &["agent", "cell", "height"],
            Pred::Transfer => &["from", "to", "asset", "amount", "height"],
            Pred::Balance => &["cell", "asset", "amount", "height"],
            Pred::Granted => &["from", "to", "cap", "height"],
            Pred::Revoked => &["cap", "height"],
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            Pred::Created => "created",
            Pred::Transfer => "transfer",
            Pred::Balance => "balance",
            Pred::Granted => "granted",
            Pred::Revoked => "revoked",
        }
    }
}

/// One ground fact: a predicate applied to ground terms. Invariants
/// (enforced by the constructors, checked by [`Fact::well_formed`]):
/// `args.len() == pred.arity()` and the last arg is `Value::Nat(height)`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Fact {
    pub pred: Pred,
    pub args: Vec<Value>,
}

impl Fact {
    pub fn created(agent: impl Into<String>, cell: impl Into<String>, h: Height) -> Self {
        Fact {
            pred: Pred::Created,
            args: vec![Value::sym(agent), Value::sym(cell), Value::nat(h)],
        }
    }

    pub fn transfer(
        from: impl Into<String>,
        to: impl Into<String>,
        asset: impl Into<String>,
        amount: u64,
        h: Height,
    ) -> Self {
        Fact {
            pred: Pred::Transfer,
            args: vec![
                Value::sym(from),
                Value::sym(to),
                Value::sym(asset),
                Value::nat(amount),
                Value::nat(h),
            ],
        }
    }

    pub fn balance(
        cell: impl Into<String>,
        asset: impl Into<String>,
        amount: u64,
        h: Height,
    ) -> Self {
        Fact {
            pred: Pred::Balance,
            args: vec![
                Value::sym(cell),
                Value::sym(asset),
                Value::nat(amount),
                Value::nat(h),
            ],
        }
    }

    pub fn granted(
        from: impl Into<String>,
        to: impl Into<String>,
        cap: impl Into<String>,
        h: Height,
    ) -> Self {
        Fact {
            pred: Pred::Granted,
            args: vec![
                Value::sym(from),
                Value::sym(to),
                Value::sym(cap),
                Value::nat(h),
            ],
        }
    }

    pub fn revoked(cap: impl Into<String>, h: Height) -> Self {
        Fact {
            pred: Pred::Revoked,
            args: vec![Value::sym(cap), Value::nat(h)],
        }
    }

    pub fn well_formed(&self) -> bool {
        self.args.len() == self.pred.arity() && matches!(self.args.last(), Some(Value::Nat(_)))
    }

    /// The height stamp (last argument).
    pub fn height(&self) -> Height {
        match self.args.last() {
            Some(Value::Nat(h)) => *h,
            _ => 0,
        }
    }
}

impl fmt::Display for Fact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}(", self.pred.name())?;
        for (i, a) in self.args.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{a}")?;
        }
        write!(f, ")")
    }
}

/// The fact base: an append-only bag of ground facts. Monotone by
/// construction — `add` is the only mutation.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct FactBase {
    facts: Vec<Fact>,
}

impl FactBase {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add(&mut self, f: Fact) {
        debug_assert!(f.well_formed(), "malformed fact: {f}");
        self.facts.push(f);
    }

    pub fn len(&self) -> usize {
        self.facts.len()
    }

    pub fn is_empty(&self) -> bool {
        self.facts.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = &Fact> {
        self.facts.iter()
    }

    /// All facts of one predicate (the per-atom scan in eval).
    pub fn with_pred(&self, p: Pred) -> impl Iterator<Item = &Fact> {
        self.facts.iter().filter(move |f| f.pred == p)
    }

    /// The maximum height stamp present — "this answer is only as fresh as
    /// height H" for finalized-dependent queries.
    pub fn max_height(&self) -> Height {
        self.facts.iter().map(|f| f.height()).max().unwrap_or(0)
    }
}
