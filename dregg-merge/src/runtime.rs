//! The merge runtime — the orchestrator that ties the gate, the CvRDT join, and
//! the mergeable receipt together into the production offchain-coordination path.
//!
//! [`MergeRuntime`] holds the head of one coordination chain (the prev-hash of
//! the next receipt). Each [`MergeRuntime::merge`] consults the [`crate::gate`]:
//! a free merge runs the CvRDT join and emits a chained [`MergeReceipt`]; a
//! non-confluent merge is **refused** with an [`Escalation`] — the caller must
//! route it through a settling turn at the boundary.

use std::collections::BTreeSet;

use crate::delta::Hash;
use crate::gate::{Escalation, MergeVerdict, classify_merge};
use crate::receipt::{DeltaProvenance, MergeReceipt, Provenance};
use crate::state::MergeState;

/// The zero hash — the genesis prev-hash of a fresh coordination chain.
pub const GENESIS: Hash = [0u8; 32];

/// A successful free merge: the merged state plus its chained receipt.
#[derive(Clone, Debug)]
pub struct MergeOutcome<S: MergeState> {
    /// The merged CvRDT state (the join of the two inputs).
    pub state: S,
    /// The verifiable, re-witnessable receipt of the merge.
    pub receipt: MergeReceipt,
}

/// The offchain merge runtime for one coordination chain. `kind_name` is the
/// human label the gate reports in escalations; `head` is the prev-hash of the
/// next receipt (advanced on every free merge).
pub struct MergeRuntime {
    kind_name: &'static str,
    producer: String,
    head: Hash,
}

impl MergeRuntime {
    /// A fresh runtime for cells of kind `kind_name`, receipts produced under
    /// `producer`, starting from the genesis prev-hash.
    pub fn new(kind_name: &'static str, producer: impl Into<String>) -> Self {
        MergeRuntime {
            kind_name,
            producer: producer.into(),
            head: GENESIS,
        }
    }

    /// The current chain head (the prev-hash the next receipt will carry).
    pub fn head(&self) -> Hash {
        self.head
    }

    /// The gate's verdict on merging `a` and `b`, without performing it.
    pub fn would_merge<S: MergeState>(&self, a: &S, b: &S) -> MergeVerdict {
        classify_merge(a, b, self.kind_name)
    }

    /// Attempt to merge two cell copies **offchain, coordination-free**.
    ///
    /// On [`Ok`] the gate found the merge I-confluent: the result is the CvRDT
    /// join (commutative, idempotent, order-independent) and a chained,
    /// re-witnessable [`MergeReceipt`] — **no consensus, no chain op**. The
    /// runtime's chain head advances to this receipt's hash.
    ///
    /// On [`Err`] the gate refused (a non-I-confluent invariant or a
    /// non-monotone op): the operation must settle at the boundary. The chain
    /// head is left unchanged.
    pub fn merge<S: MergeState>(&mut self, a: &S, b: &S) -> Result<MergeOutcome<S>, Escalation> {
        match classify_merge(a, b, self.kind_name) {
            MergeVerdict::Settle(e) => Err(e),
            MergeVerdict::Free => {
                let state = a.join(b);
                let provenance = provenance_of(a, b);
                let receipt = MergeReceipt {
                    cell: a.cell_id().to_string(),
                    input_a: a.commitment(),
                    input_b: b.commitment(),
                    merged: state.commitment(),
                    provenance,
                    class: state.coordination_class(),
                    producer: self.producer.clone(),
                    prev_receipt_hash: self.head,
                };
                // a free merge is, by the gate, always monotone — the merged
                // class is Monotone; assert it (defense in depth).
                debug_assert_eq!(
                    receipt.class,
                    dregg_query::CoordinationClass::Monotone,
                    "a free merge must be monotone"
                );
                // the invariant survives an I-confluent merge (admits_sound).
                debug_assert!(
                    state.invariant(),
                    "I-confluent merge preserves the invariant"
                );
                self.head = receipt.receipt_hash();
                Ok(MergeOutcome { state, receipt })
            }
        }
    }
}

/// Per-element provenance of a merge: for every element id in either copy, mark
/// it `A` / `B` / `Both`. Sorted by content id (canonical, order-independent).
fn provenance_of<S: MergeState>(a: &S, b: &S) -> Vec<DeltaProvenance> {
    let ia = a.element_ids();
    let ib = b.element_ids();
    let all: BTreeSet<Hash> = ia.union(&ib).copied().collect();
    all.into_iter()
        .map(|delta| {
            let from = match (ia.contains(&delta), ib.contains(&delta)) {
                (true, true) => Provenance::Both,
                (true, false) => Provenance::A,
                (false, true) => Provenance::B,
                (false, false) => unreachable!("id came from the union of a and b"),
            };
            DeltaProvenance { delta, from }
        })
        .collect()
}
