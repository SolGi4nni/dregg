//! The **mergeable receipt** — the verifiable trace a free merge leaves, with
//! no chain op.
//!
//! A [`MergeReceipt`] is the offchain-coordination artifact: it records the
//! merged state's commitment, the provenance of the merged operations (which
//! deltas came from which party), and a prev-hash chain — the same append-only,
//! prev-hash-chained, non-witness-verifiable discipline the architecture critique
//! praised in `TurnReceipt` / `BridgeReceipt` (§1.1), now on the *write/merge*
//! side. A third party who holds the two input states can [`MergeReceipt::rewitness`]
//! it: recompute the join and check the commitment matches — convincing a peer
//! who *was not there*, with no consensus and no chain op.
//!
//! The receipt's `receipt_hash` is a 32-byte commitment of the same width the
//! read face's MMR consumes (`dregg_query::mmr`), so a *stream* of merge receipts
//! composes as MMR leaves and carries the read face's non-omission certificate
//! (see `tests/`): the whole offchain-coordination trace is re-witnessable
//! end-to-end without a chain op per merge.

use serde::{Deserialize, Serialize};
use thiserror::Error;

use dregg_query::CoordinationClass;

use crate::delta::Hash;
use crate::state::MergeState;

/// One merged operation's provenance: which delta (by content id) the merge
/// absorbed, and from which party's copy it came. `from_both` marks a delta the
/// two copies shared (the union deduplicated it — the idempotence witness).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DeltaProvenance {
    /// The delta's content id (hex on the wire would be the caller's choice;
    /// kept as raw bytes here).
    pub delta: Hash,
    /// The party whose copy contributed it (`"a"` / `"b"`), or that it was in
    /// both.
    pub from: Provenance,
}

/// Which side a merged delta came from.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Provenance {
    /// Only in party A's copy.
    A,
    /// Only in party B's copy.
    B,
    /// In both copies — the union deduplicated it (idempotence).
    Both,
}

/// The verifiable record of one free merge.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MergeReceipt {
    /// The cell merged.
    pub cell: String,
    /// The commitment of party A's input state.
    pub input_a: Hash,
    /// The commitment of party B's input state.
    pub input_b: Hash,
    /// The commitment of the **merged** state — the re-witness target.
    pub merged: Hash,
    /// The provenance of every delta the merge absorbed (sorted by content id —
    /// canonical, so the receipt is order-independent like the merge).
    pub provenance: Vec<DeltaProvenance>,
    /// The CALM grade of the merged state (monotone — a free merge is always
    /// monotone, since a non-monotone op would have forced a settle).
    pub class: CoordinationClass,
    /// The producing party (sign-ready; an unverified claim until a sig is
    /// demanded).
    pub producer: String,
    /// The previous merge receipt's hash in this coordination chain
    /// (append-only, prev-hash-chained — the `TurnReceipt` discipline). The
    /// genesis receipt carries the zero hash.
    pub prev_receipt_hash: Hash,
}

const TAG_RECEIPT: &[u8] = b"dregg-merge-receipt-v1";

impl MergeReceipt {
    /// The 32-byte receipt commitment — a domain-tagged blake3 over the receipt
    /// fields, suitable as an MMR leaf (`dregg_query::mmr`). This is what chains
    /// receipts and what a receipt-log root commits.
    pub fn receipt_hash(&self) -> Hash {
        let mut h = blake3::Hasher::new();
        h.update(TAG_RECEIPT);
        h.update(&(self.cell.len() as u64).to_le_bytes());
        h.update(self.cell.as_bytes());
        h.update(&self.input_a);
        h.update(&self.input_b);
        h.update(&self.merged);
        h.update(&(self.provenance.len() as u64).to_le_bytes());
        for p in &self.provenance {
            h.update(&p.delta);
            h.update(&[match p.from {
                Provenance::A => 0,
                Provenance::B => 1,
                Provenance::Both => 2,
            }]);
        }
        h.update(&[match self.class {
            CoordinationClass::Monotone => 0,
            CoordinationClass::FinalizedDependent => 1,
        }]);
        h.update(&(self.producer.len() as u64).to_le_bytes());
        h.update(self.producer.as_bytes());
        h.update(&self.prev_receipt_hash);
        *h.finalize().as_bytes()
    }

    /// **Re-witness** the merge: given the two input states the receipt names,
    /// recompute the join and check that
    ///
    /// 1. the input commitments match the receipt's `input_a` / `input_b`;
    /// 2. the recomputed merged commitment matches the receipt's `merged`;
    /// 3. the carried class matches the recomputed merged state's grade.
    ///
    /// On `Ok`, a third party who was not present is convinced the merge is the
    /// genuine CvRDT join of exactly these inputs — no chain op, no consensus.
    pub fn rewitness<S: MergeState>(&self, a: &S, b: &S) -> Result<(), RewitnessError> {
        if a.commitment() != self.input_a {
            return Err(RewitnessError::InputAMismatch);
        }
        if b.commitment() != self.input_b {
            return Err(RewitnessError::InputBMismatch);
        }
        let merged = a.join(b);
        if merged.commitment() != self.merged {
            return Err(RewitnessError::MergedMismatch);
        }
        if merged.coordination_class() != self.class {
            return Err(RewitnessError::ClassMismatch);
        }
        Ok(())
    }
}

/// Why a re-witness failed — each is a tamper/forgery tooth.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
pub enum RewitnessError {
    #[error("party A's input commitment does not match the receipt")]
    InputAMismatch,
    #[error("party B's input commitment does not match the receipt")]
    InputBMismatch,
    #[error("the recomputed merged commitment does not match the receipt")]
    MergedMismatch,
    #[error("the recomputed coordination class does not match the receipt")]
    ClassMismatch,
}
