//! The **confluence gate** — only I-confluent operations merge freely; anything
//! else must settle at the boundary.
//!
//! This is the Rust face of `metatheory/Dregg2/Confluence.lean`
//! (`IConfluent` / `Tier1Eligible` / `admits_sound` / `nonpairwise_escalation`)
//! and `Dregg2/Confluence/SemanticConvergence.lean` (`classifyAliased` /
//! `classify_sound`). The gate reads the *static* invariant class
//! ([`MergeState::is_iconfluent_kind`]) and the *value-level* coordination grade
//! ([`MergeState::coordination_class`]) and renders one of two verdicts:
//!
//! - [`MergeVerdict::Free`] — both operands are I-confluent (a grow-only set with
//!   no retraction). The merge is the CvRDT join, coordination-free, no consensus,
//!   no chain op. This is `admits_sound`: concurrent invariant-preserving versions
//!   merge invariant-safely.
//! - [`MergeVerdict::Settle`] — a non-I-confluent invariant or a non-monotone op
//!   participates. The merge crosses the conservation/authority boundary and must
//!   go through a settling turn — the one place revocation is non-monotone
//!   (`SettlementSoundness.lean`). This is `nonpairwise_escalation`: a constructive
//!   clash, not a mere declaration.
//!
//! ## NAMED SEAM (for the circuit swarm)
//!
//! The Lean gate reasons over the abstract lattice `⊔`. That THIS crate's
//! [`MergeState::join`] **IS** that `⊔`, and that a verified merge is witnessed
//! in-circuit so a *light client* (not only a re-executing peer) sees the merge
//! preserved the invariant, is the **`MergeRefinesConfluence` weld** — the same
//! VK-epoch shape the read face names for `CommitBindsMMR`. The runtime here is
//! executor-grade (a re-witnessing peer is convinced); the in-circuit tooth is
//! its named shadow. No new Lean theorem is added by this crate.

use thiserror::Error;

use crate::state::MergeState;

/// Why a merge cannot proceed offchain coordination-free — it must settle.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum Escalation {
    /// The cell's invariant is structurally non-I-confluent (a bounded
    /// resource — `balance ≥ 0`). Concurrent operations can each be locally
    /// valid yet merge to a violation (`is_iconfluent_kind() == false`). The
    /// merge must settle at the boundary (a conserving turn that re-checks the
    /// invariant against the certified prefix).
    #[error(
        "non-I-confluent invariant: this cell kind ({kind}) is not tier-1 eligible \
         (a bounded resource; concurrent versions can merge to a violation) — \
         the merge must settle at the boundary"
    )]
    NonIConfluentKind { kind: &'static str },

    /// A non-monotone op (a retraction/negation) participates in one of the
    /// operands, so the merge is `FinalizedDependent`: an asserted fact can
    /// become absent. The retraction must settle (its effect is only correct
    /// relative to a finalized prefix — `negation_retracts`).
    #[error(
        "non-monotone op participates (a retraction/negation): the merge is \
         finalized-dependent and must settle at the boundary"
    )]
    NonMonotoneOp,
}

/// The gate's verdict on a proposed merge.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MergeVerdict {
    /// Both operands are I-confluent — merge freely, coordination-free.
    Free,
    /// The merge must settle at the boundary, with the reason.
    Settle(Escalation),
}

impl MergeVerdict {
    /// `true` iff the merge may proceed offchain coordination-free.
    pub fn is_free(&self) -> bool {
        matches!(self, MergeVerdict::Free)
    }
}

/// Classify a proposed merge of two cell copies.
///
/// The order of checks matters only for the *reason* reported, not the verdict:
/// the structural (kind-level) non-confluence is checked first because it
/// applies to every value of the type; then the value-level non-monotone reason.
/// A merge is [`MergeVerdict::Free`] iff the cell kind is I-confluent **and**
/// neither operand carries a non-monotone op.
pub fn classify_merge<S: MergeState>(a: &S, b: &S, kind_name: &'static str) -> MergeVerdict {
    use dregg_query::CoordinationClass::FinalizedDependent;

    if !S::is_iconfluent_kind() {
        return MergeVerdict::Settle(Escalation::NonIConfluentKind { kind: kind_name });
    }
    if a.coordination_class() == FinalizedDependent || b.coordination_class() == FinalizedDependent
    {
        return MergeVerdict::Settle(Escalation::NonMonotoneOp);
    }
    MergeVerdict::Free
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::delta::Delta;
    use crate::state::{BoundedCounter, GrowSet};

    #[test]
    fn grow_only_merge_is_free() {
        let mut a = GrowSet::new("c");
        a.apply(Delta::assert("c", b"x".to_vec(), "alice"));
        let mut b = GrowSet::new("c");
        b.apply(Delta::assert("c", b"y".to_vec(), "bob"));
        assert!(classify_merge(&a, &b, "GrowSet").is_free());
    }

    #[test]
    fn retraction_forces_settle() {
        let mut a = GrowSet::new("c");
        let id = a.apply(Delta::assert("c", b"x".to_vec(), "alice"));
        a.apply(Delta::retract("c", id, "alice")); // a negation participates
        let b = GrowSet::new("c");
        match classify_merge(&a, &b, "GrowSet") {
            MergeVerdict::Settle(Escalation::NonMonotoneOp) => {}
            v => panic!("expected NonMonotoneOp settle, got {v:?}"),
        }
    }

    #[test]
    fn bounded_counter_always_settles() {
        let a = BoundedCounter::new("c");
        let b = BoundedCounter::new("c");
        match classify_merge(&a, &b, "BoundedCounter") {
            MergeVerdict::Settle(Escalation::NonIConfluentKind { .. }) => {}
            v => panic!("expected NonIConfluentKind settle, got {v:?}"),
        }
    }
}
