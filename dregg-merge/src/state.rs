//! The mergeable cell state — a CvRDT join-semilattice, the Rust face of
//! `Dregg2.Confluence.MergeState` (`SemilatticeSup`).
//!
//! Two concrete states realize the two polarities `Confluence.lean` witnesses
//! concretely (`top_iconfluent` vs `cardLeOne_not_iconfluent`):
//!
//! - [`GrowSet`] — a grow-only set of content-addressed deltas (plus tombstones).
//!   The G-Set CvRDT (`merge = ∪`). I-confluent in the no-negation fragment; a
//!   tombstone flips it `FinalizedDependent` (the `survivors = asserted \ negated`
//!   non-monotone reason).
//! - [`BoundedCounter`] — a PN-Counter under the `balance ≥ 0` invariant. NOT
//!   I-confluent: two locally-valid concurrent decrements merge to an overdraft
//!   (the `nonpairwise_escalation` clashing pair, in Rust).

use std::collections::{BTreeMap, BTreeSet};

use dregg_query::CoordinationClass;

use crate::delta::{Delta, Hash, OpKind};

/// A CvRDT join-semilattice cell state — the mergeable object.
///
/// [`MergeState::join`] MUST satisfy the CRDT laws (commutative, associative,
/// idempotent), so concurrent versions **converge regardless of merge order**
/// with no coordination — the `⊔` of `Dregg2.Confluence.MergeState`. The merge
/// runtime relies on these laws; the test suite exercises them on every impl.
pub trait MergeState: Sized + Clone + PartialEq {
    /// The cell id this state is a copy of — a merge only unifies copies of the
    /// *same* cell.
    fn cell_id(&self) -> &str;

    /// The deterministic CvRDT join (`⊔`). Coordination-free convergence.
    fn join(&self, other: &Self) -> Self;

    /// The cell invariant `I` (e.g. `balance ≥ 0`). Admissible states satisfy it.
    /// (`Dregg2.Confluence.Invariant`.)
    fn invariant(&self) -> bool;

    /// **Type-level I-confluence** — whether this *kind* of cell's invariant is
    /// I-confluent (`Dregg2.Confluence.IConfluent` / `Tier1Eligible`): does
    /// every pair of invariant-preserving versions merge invariant-safely? This
    /// is a static property of the invariant, independent of the value — a
    /// grow-only set is `true`, a bounded resource is `false`.
    fn is_iconfluent_kind() -> bool;

    /// **Value-level coordination grade** — `Monotone` unless a non-monotone op
    /// participates in *this* value (a tombstone/retraction). Mirrors
    /// `dregg_query::classify` exactly: monotone = coordination-free; finalized-
    /// dependent = a negation participates, so a row/alias may retract.
    fn coordination_class(&self) -> CoordinationClass;

    /// A 32-byte content commitment of the state — re-witnessable: a third party
    /// who reconstructs the state recomputes the same commitment. Must be
    /// order-independent (it commits a *set*, not a sequence).
    fn commitment(&self) -> Hash;

    /// The content ids of the state's elements, for per-element merge
    /// provenance (which party contributed each). Defaults to empty for states
    /// that are not element-sets (e.g. counters, which never reach a free
    /// merge); [`GrowSet`] overrides it with its asserted ∪ negated ids.
    fn element_ids(&self) -> BTreeSet<Hash> {
        BTreeSet::new()
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// GrowSet — the G-Set CvRDT (the I-confluent witness; tombstone = the one
// non-monotone reason).
// ─────────────────────────────────────────────────────────────────────────────

/// A grow-only set of content-addressed deltas on one cell, plus grow-only
/// tombstones (retractions). The G-Set CvRDT: `join = ∪`. The *survivors* —
/// the live state — are `asserted \ negated` (mirrors
/// `SemanticConvergence.survivors`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GrowSet {
    /// The cell id.
    pub cell: String,
    /// Asserted deltas, keyed by content id (the key dedups — idempotence).
    pub asserted: BTreeMap<Hash, Delta>,
    /// Tombstones: content ids of retracted deltas (grow-only). Non-empty ⇒
    /// `FinalizedDependent`.
    pub negated: BTreeSet<Hash>,
}

impl GrowSet {
    /// An empty grow-set for `cell`.
    pub fn new(cell: impl Into<String>) -> Self {
        GrowSet {
            cell: cell.into(),
            asserted: BTreeMap::new(),
            negated: BTreeSet::new(),
        }
    }

    /// Apply one local op to this copy (offchain, no coordination). An
    /// [`OpKind::Assert`] grows `asserted`; an [`OpKind::Retract`] grows
    /// `negated` with its target. Returns the delta's content id.
    ///
    /// Panics if the delta's `cell` does not match (a merge only unifies copies
    /// of the *same* cell).
    pub fn apply(&mut self, d: Delta) -> Hash {
        assert_eq!(d.cell, self.cell, "delta cell must match the GrowSet cell");
        let id = d.id();
        match d.kind {
            OpKind::Assert => {
                self.asserted.insert(id, d);
            }
            OpKind::Retract => {
                if let Some(t) = d.target {
                    self.negated.insert(t);
                }
                // the retraction is itself a delta in the grow-only record.
                self.asserted.insert(id, d);
            }
        }
        id
    }

    /// The live survivors — `asserted \ negated` (the deltas not retracted).
    pub fn survivors(&self) -> impl Iterator<Item = &Delta> {
        self.asserted
            .iter()
            .filter(|(id, _)| !self.negated.contains(*id))
            .map(|(_, d)| d)
    }
}

const TAG_GROWSET: &[u8] = b"dregg-merge-growset-v1";

impl MergeState for GrowSet {
    fn cell_id(&self) -> &str {
        &self.cell
    }

    fn join(&self, other: &Self) -> Self {
        debug_assert_eq!(self.cell, other.cell, "join unifies copies of one cell");
        let mut asserted = self.asserted.clone();
        for (id, d) in &other.asserted {
            asserted.entry(*id).or_insert_with(|| d.clone());
        }
        let mut negated = self.negated.clone();
        negated.extend(other.negated.iter().copied());
        GrowSet {
            cell: self.cell.clone(),
            asserted,
            negated,
        }
    }

    fn invariant(&self) -> bool {
        // grow-only: the `True` invariant of `top_iconfluent` — any merge keeps it.
        true
    }

    fn is_iconfluent_kind() -> bool {
        // a grow-only set passes the static tier-1 gate (`aliasedRaw_tier1`).
        true
    }

    fn coordination_class(&self) -> CoordinationClass {
        // monotone iff no retraction participates — exactly `classifyAliased`.
        if self.negated.is_empty() {
            CoordinationClass::Monotone
        } else {
            CoordinationClass::FinalizedDependent
        }
    }

    fn commitment(&self) -> Hash {
        // commit the SET: fold sorted ids (BTree gives canonical order), tagged
        // by role, so the commitment is order-independent and re-witnessable.
        let mut h = blake3::Hasher::new();
        h.update(TAG_GROWSET);
        h.update(self.cell.as_bytes());
        h.update(&[0]);
        for id in self.asserted.keys() {
            h.update(b"a");
            h.update(id);
        }
        for id in &self.negated {
            h.update(b"n");
            h.update(id);
        }
        *h.finalize().as_bytes()
    }

    fn element_ids(&self) -> BTreeSet<Hash> {
        // every delta the copy carries — asserted ids plus tombstone targets —
        // so provenance covers retractions too.
        let mut ids: BTreeSet<Hash> = self.asserted.keys().copied().collect();
        ids.extend(self.negated.iter().copied());
        ids
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// BoundedCounter — the PN-Counter under `balance >= 0` (the NON-I-confluent
// witness; the `cardLeOne_not_iconfluent` / `balance >= 0` shape).
// ─────────────────────────────────────────────────────────────────────────────

/// A PN-Counter under the `balance ≥ 0` invariant: per-replica grow-only
/// `credits` and `debits` (so the join is a pointwise max — a true CvRDT), with
/// `balance = Σcredits − Σdebits`.
///
/// This is NOT I-confluent. Each replica's local decrements can keep its own
/// balance `≥ 0`, yet the merge (pointwise max ⇒ the debits SUM) can drive the
/// merged balance negative — `nonpairwise_escalation`'s clashing pair. The gate
/// therefore refuses a free merge of these (they must settle at the boundary).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BoundedCounter {
    /// The cell id.
    pub cell: String,
    /// Per-replica total credits (grow-only — a G-Counter).
    pub credits: BTreeMap<String, u64>,
    /// Per-replica total debits (grow-only — a G-Counter).
    pub debits: BTreeMap<String, u64>,
}

impl BoundedCounter {
    /// A fresh counter for `cell`.
    pub fn new(cell: impl Into<String>) -> Self {
        BoundedCounter {
            cell: cell.into(),
            credits: BTreeMap::new(),
            debits: BTreeMap::new(),
        }
    }

    /// Replica `who` credits `amount` (grow-only on its own credit register).
    pub fn credit(&mut self, who: impl Into<String>, amount: u64) {
        *self.credits.entry(who.into()).or_default() += amount;
    }

    /// Replica `who` debits `amount` (grow-only on its own debit register).
    pub fn debit(&mut self, who: impl Into<String>, amount: u64) {
        *self.debits.entry(who.into()).or_default() += amount;
    }

    /// The signed balance: `Σcredits − Σdebits` (may be negative after a merge
    /// the gate would have refused — that negativity is the invariant violation).
    pub fn balance(&self) -> i128 {
        let c: u128 = self.credits.values().map(|v| *v as u128).sum();
        let d: u128 = self.debits.values().map(|v| *v as u128).sum();
        c as i128 - d as i128
    }
}

const TAG_COUNTER: &[u8] = b"dregg-merge-pncounter-v1";

impl MergeState for BoundedCounter {
    fn cell_id(&self) -> &str {
        &self.cell
    }

    fn join(&self, other: &Self) -> Self {
        debug_assert_eq!(self.cell, other.cell, "join unifies copies of one cell");
        let mut credits = self.credits.clone();
        for (k, v) in &other.credits {
            let e = credits.entry(k.clone()).or_default();
            *e = (*e).max(*v); // pointwise max — the G-Counter CvRDT join.
        }
        let mut debits = self.debits.clone();
        for (k, v) in &other.debits {
            let e = debits.entry(k.clone()).or_default();
            *e = (*e).max(*v);
        }
        BoundedCounter {
            cell: self.cell.clone(),
            credits,
            debits,
        }
    }

    fn invariant(&self) -> bool {
        self.balance() >= 0
    }

    fn is_iconfluent_kind() -> bool {
        // `balance >= 0` is linear but NOT I-confluent (Confluence.lean header):
        // two withdrawals merge to overdraft. The static gate is `false`.
        false
    }

    fn coordination_class(&self) -> CoordinationClass {
        // a bounded counter is always finalized-dependent: its merged balance
        // depends on the certified prefix of contributions.
        CoordinationClass::FinalizedDependent
    }

    fn commitment(&self) -> Hash {
        let mut h = blake3::Hasher::new();
        h.update(TAG_COUNTER);
        h.update(self.cell.as_bytes());
        h.update(&[0]);
        for (k, v) in &self.credits {
            h.update(b"c");
            h.update(k.as_bytes());
            h.update(&v.to_le_bytes());
        }
        for (k, v) in &self.debits {
            h.update(b"d");
            h.update(k.as_bytes());
            h.update(&v.to_le_bytes());
        }
        *h.finalize().as_bytes()
    }
}
