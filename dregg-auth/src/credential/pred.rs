//! The caveat predicate language — the Boolean algebra over the proven atom
//! shapes.
//!
//! Every constructor here mirrors a named shape in the Lean development under
//! `metatheory/Dregg2/`; the doc comment on each variant names its counterpart.
//! The Boolean layer is `Dregg2.Exec.PredAlgebra.Pred` (`atom`/`tt`/`ff`/`and`/
//! `or`/`not`/`allOf`/`anyOf` with `not` at EVERY level); the temporal atoms are
//! `Dregg2.Authority.TemporalAlgebra.TemporalAtom`; the attribute atoms are the
//! `Exec.Program.SimpleConstraint` shapes.
//!
//! ## Evaluation discipline (fail-closed, even under `Not`)
//!
//! The Lean `Pred.eval` is total over a fully-bound record. A verification
//! [`Context`](super::Context) is *partial* — the caller may not have supplied a
//! clock or an attribute. We therefore evaluate three-valuedly: a predicate that
//! mentions data the context does not bind does not evaluate to `false` (which
//! `Not` would flip into authority!) — it returns [`Unbound`], and the top-level
//! verdict is a refusal. On contexts that bind everything a predicate mentions,
//! the semantics coincide exactly with the Lean `Pred.eval` fold.

use serde::{Deserialize, Serialize};

use super::caveat::Context;

/// Why a predicate could not be evaluated: the context failed to bind data the
/// predicate mentions. Always a refusal at the top level — missing data is
/// never `false` (so [`Pred::Not`] can never convert absence into authority).
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum Unbound {
    /// A temporal atom was evaluated but the context supplied no clock.
    #[error("the context supplies no clock, and the caveat is temporal")]
    Clock,
    /// An attribute atom named a key the context does not bind.
    #[error("the context does not bind attribute `{0}`")]
    Attr(String),
}

/// A first-party caveat predicate over the verification [`Context`].
///
/// This is the *caveat language*: the exact atom shapes the Lean development
/// proves things about, under the clean Boolean algebra of
/// `Dregg2.Exec.PredAlgebra.Pred`. Composition is fail-closed: `AllOf([])`
/// admits (it constrains nothing — `Pred.evalAll [] = true`) while `AnyOf([])`
/// REFUSES (`Pred.evalAny [] = false`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Pred {
    /// Top — admits everything. Lean: `Pred.tt` (PredAlgebra.lean); appending
    /// it is the trivial attenuation (`Authority.Caveat.attenuate_trivial`).
    True,
    /// Bottom — admits nothing. Lean: `Pred.ff`.
    False,
    /// Attribute equality: the context must bind `key` to exactly `value`.
    /// Lean shape: the equality atom `SimpleConstraint.fieldEquals`
    /// (Exec/Program.lean), lifted into the algebra via `Pred.ofSimple`.
    AttrEq {
        /// The request attribute inspected (e.g. `tool`, `path`, `actor`).
        key: String,
        /// The exact value required.
        value: String,
    },
    /// Attribute prefix containment: the context must bind `key` to a value
    /// that starts with `prefix`. Lean shape: `SimpleConstraint.prefixOf`
    /// (Exec/Program.lean, admit-characterized by `evalSimple_prefixOf_iff`) —
    /// the namespace/path-containment atom, here over the string's character
    /// path.
    AttrPrefix {
        /// The request attribute inspected.
        key: String,
        /// The required prefix.
        prefix: String,
    },
    /// Admit iff `clock >= at` — the vesting / activation gate. Lean:
    /// `TemporalAtom.afterHeight` (TemporalAlgebra.lean), proven upward-closed
    /// (`afterHeight_upward_closed`: once it admits, it admits forever after).
    NotBefore {
        /// The clock reading (unix seconds or block height — the deployment's
        /// one monotone clock) at which the credential activates.
        at: u64,
    },
    /// Admit iff `clock <= at` — the deadline / expiry gate. Lean:
    /// `TemporalAtom.beforeHeight`, proven downward-closed
    /// (`beforeHeight_downward_closed`).
    NotAfter {
        /// The clock reading after which every check refuses.
        at: u64,
    },
    /// Admit iff `not_before <= clock <= not_after` — the two-sided validity
    /// window. Lean: `TemporalAtom.withinWindow`, which is *proven* to be the
    /// meet of an `afterHeight` and a `beforeHeight`
    /// (`withinWindow_eq_after_and_before`).
    Within {
        /// Window opening (inclusive).
        not_before: u64,
        /// Window closing (inclusive).
        not_after: u64,
    },
    /// n-ary conjunction. Lean: `Pred.allOf` via `Pred.evalAll` — the empty
    /// conjunction admits (`evalAll [] = true`: no constraint installed).
    AllOf(Vec<Pred>),
    /// n-ary disjunction. Lean: `Pred.anyOf` via `Pred.evalAny` — the empty
    /// disjunction REFUSES (`evalAny [] = false`): fail-closed.
    AnyOf(Vec<Pred>),
    /// Negation, available at every level (the PredAlgebra fix over the legacy
    /// 2-level grammar). Lean: `Pred.not` (`Pred.eval_not`; double negation
    /// collapses, `Pred.eval_not_not`; De Morgan holds, `Pred.deMorgan_and`).
    ///
    /// Negation never applies to third-party caveats — that is inexpressible
    /// by construction ([`Caveat`](super::Caveat) separates the two layers,
    /// exactly as `Dregg2.Authority.Caveat` keeps `thirdParty` outside the
    /// local predicate).
    Not(Box<Pred>),
}

impl Pred {
    /// Evaluate against a context — the executable mirror of the Lean
    /// `Pred.eval` fold (PredAlgebra.lean), three-valued only in that data the
    /// context fails to bind yields `Err(Unbound)` rather than `false`, so the
    /// top level can refuse outright (fail-closed even under [`Pred::Not`]).
    pub fn eval(&self, ctx: &Context) -> Result<bool, Unbound> {
        match self {
            Pred::True => Ok(true),
            Pred::False => Ok(false),
            Pred::AttrEq { key, value } => match ctx.lookup_attr(key) {
                Some(v) => Ok(v == value),
                None => Err(Unbound::Attr(key.clone())),
            },
            Pred::AttrPrefix { key, prefix } => match ctx.lookup_attr(key) {
                Some(v) => Ok(v.starts_with(prefix.as_str())),
                None => Err(Unbound::Attr(key.clone())),
            },
            Pred::NotBefore { at } => Ok(*at <= ctx.clock().ok_or(Unbound::Clock)?),
            Pred::NotAfter { at } => Ok(ctx.clock().ok_or(Unbound::Clock)? <= *at),
            Pred::Within {
                not_before,
                not_after,
            } => {
                let clock = ctx.clock().ok_or(Unbound::Clock)?;
                // The meet of the two one-sided gates —
                // `withinWindow_eq_after_and_before`, executably.
                Ok(*not_before <= clock && clock <= *not_after)
            }
            Pred::AllOf(ps) => {
                // `Pred.evalAll`: empty ⇒ true; one Unbound poisons the meet.
                for p in ps {
                    if !p.eval(ctx)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Pred::AnyOf(ps) => {
                // `Pred.evalAny`: empty ⇒ FALSE (fail-closed). An unbound arm
                // refuses the whole disjunction: we cannot know it would not
                // have been the admitting arm.
                for p in ps {
                    if p.eval(ctx)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            Pred::Not(p) => Ok(!p.eval(ctx)?),
        }
    }

    /// One-line human prose for this predicate — the explain convention of
    /// `sdk/src/explain.rs`: a structural reading of the variant's fields,
    /// exhaustive with no `_ =>` arm so every future variant must acquire one.
    pub fn explain(&self) -> String {
        match self {
            Pred::True => "always".to_string(),
            Pred::False => "never".to_string(),
            Pred::AttrEq { key, value } => format!("attribute `{key}` = `{value}`"),
            Pred::AttrPrefix { key, prefix } => {
                format!("attribute `{key}` starts with `{prefix}`")
            }
            Pred::NotBefore { at } => format!("not before clock {at} (vesting gate)"),
            Pred::NotAfter { at } => format!("not after clock {at} (expiry gate)"),
            Pred::Within {
                not_before,
                not_after,
            } => format!("within clock window [{not_before}, {not_after}]"),
            Pred::AllOf(ps) => {
                if ps.is_empty() {
                    "all of () — no constraint".to_string()
                } else {
                    format!("all of ({})", explain_list(ps))
                }
            }
            Pred::AnyOf(ps) => {
                if ps.is_empty() {
                    "any of () — refuses (fail-closed)".to_string()
                } else {
                    format!("any of ({})", explain_list(ps))
                }
            }
            Pred::Not(p) => format!("not ({})", p.explain()),
        }
    }
}

fn explain_list(ps: &[Pred]) -> String {
    ps.iter().map(Pred::explain).collect::<Vec<_>>().join("; ")
}
