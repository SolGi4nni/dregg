//! The mergeable object's atom — a content-addressed **delta** (the rhizomatic
//! L1 shape, `~/dev/rhizomatic/spec/01-delta.md`), applied to dregg cells.
//!
//! A delta is simultaneously an *assertion* (a claim by an author), a
//! *hyperedge* (here: an op on a named cell), and a *CRDT element* (a member of
//! a grow-only set whose merge is union). It is **not** an instruction — it
//! carries no operational state. Its identity is its content hash, so:
//!
//! - anyone can derive any delta's id (no instance mints identity);
//! - identical claims by the same author **are the same delta** — a G-Set union
//!   deduplicates them, which is exactly what makes union **idempotent**;
//! - a retraction pins what it retracts by content address (a Merkle link),
//!   so tamper-evidence is structural (rhizomatic §4 / §7).
//!
//! This mirrors `Dregg2/Confluence/SemanticConvergence.lean`'s `Mapping` /
//! `Store` objects (a grow-only `asserted` set + grow-only `negated` set), the
//! content-derived-identity discharge of `sameEntity_dedup_by_content`, and the
//! dregg ids the read face already speaks (content-derived).

use serde::{Deserialize, Serialize};

/// A 32-byte content commitment — the same width as the read face's MMR leaves
/// (`dregg_query::mmr`) and the kernel receipt hash (`b"dregg-receipt-v3"`).
pub type Hash = [u8; 32];

/// The kind of operation a delta carries — the datum the [`crate::gate`] reads
/// to classify a merge. The dichotomy is exactly `Confluence.lean`'s: the
/// grow-only contributions are I-confluent; the retraction is the one
/// non-monotone reason (`negation_retracts` / `CoordinationClass::FinalizedDependent`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum OpKind {
    /// A grow-only assertion — adds the delta to the cell's grow-set. Monotone,
    /// I-confluent: once asserted it never retracts as more deltas arrive
    /// (`aliased_mono` / `top_iconfluent`). Merges coordination-free.
    Assert,
    /// A **retraction** of a prior delta, cited by content id in
    /// [`Delta::target`] (the rhizomatic negation: a delta whose pointer
    /// `negates` a `DeltaRef`). This is the single non-monotone operator on the
    /// grow-only surface — an answer present can become absent — so a merge in
    /// which a retraction participates is NOT free; it must settle at the
    /// boundary (`negation_retracts`, the CALM `finalizedDependent` cause).
    Retract,
}

/// A content-addressed delta: an op (`kind`) on a named `cell`, carrying an
/// opaque `payload`, authored `by`, optionally citing the delta it retracts.
///
/// The `id` is **not** stored — it is *derived* from the claim fields by
/// [`Delta::id`] (content addressing), so two byte-identical claims have the
/// same id and a set union deduplicates them.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Delta {
    /// The cell this op applies to (the mergeable object's id).
    pub cell: String,
    /// The operation kind (the gate's input).
    pub kind: OpKind,
    /// The opaque value the assertion carries (a content-addressed fragment).
    pub payload: Vec<u8>,
    /// The author of the claim (sign-ready; an unverified claim until a sig is
    /// demanded — rhizomatic §5).
    pub by: String,
    /// For [`OpKind::Retract`], the content id of the delta being retracted (the
    /// Merkle link). `None` for an [`OpKind::Assert`].
    pub target: Option<Hash>,
}

impl Delta {
    /// A grow-only assertion on `cell` carrying `payload`, authored `by`.
    pub fn assert(
        cell: impl Into<String>,
        payload: impl Into<Vec<u8>>,
        by: impl Into<String>,
    ) -> Self {
        Delta {
            cell: cell.into(),
            kind: OpKind::Assert,
            payload: payload.into(),
            by: by.into(),
            target: None,
        }
    }

    /// A retraction of the delta with content id `target`.
    pub fn retract(cell: impl Into<String>, target: Hash, by: impl Into<String>) -> Self {
        Delta {
            cell: cell.into(),
            kind: OpKind::Retract,
            payload: Vec::new(),
            by: by.into(),
            target: Some(target),
        }
    }

    /// The delta's **content id** — a domain-tagged, length-prefixed blake3 over
    /// its claim fields. Deterministic and canonical: the encoding fixes a field
    /// order and length-prefixes every variable-width part, so distinct claims
    /// can never collide by concatenation ambiguity. Excludes nothing derived
    /// (there is no separate sig field in this minimal core).
    pub fn id(&self) -> Hash {
        content_id(self)
    }
}

const TAG_DELTA: &[u8] = b"dregg-merge-delta-v1";

fn put_bytes(h: &mut blake3::Hasher, field: &[u8], value: &[u8]) {
    // length-prefix BOTH the field tag and the value so no two field layouts can
    // alias by concatenation (the canonical-encoding discipline).
    h.update(&(field.len() as u64).to_le_bytes());
    h.update(field);
    h.update(&(value.len() as u64).to_le_bytes());
    h.update(value);
}

/// The canonical content commitment of a delta (the body of [`Delta::id`]).
pub fn content_id(d: &Delta) -> Hash {
    let mut h = blake3::Hasher::new();
    h.update(TAG_DELTA);
    put_bytes(&mut h, b"cell", d.cell.as_bytes());
    let kind = match d.kind {
        OpKind::Assert => b"assert".as_slice(),
        OpKind::Retract => b"retract".as_slice(),
    };
    put_bytes(&mut h, b"kind", kind);
    put_bytes(&mut h, b"payload", &d.payload);
    put_bytes(&mut h, b"by", d.by.as_bytes());
    match d.target {
        Some(t) => put_bytes(&mut h, b"target", &t),
        None => put_bytes(&mut h, b"target", &[]),
    }
    *h.finalize().as_bytes()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn content_addressing_is_deterministic_and_dedups() {
        let a = Delta::assert("cell-1", b"v".to_vec(), "alice");
        let b = Delta::assert("cell-1", b"v".to_vec(), "alice");
        // identical claims => same id (a union deduplicates them — idempotence).
        assert_eq!(a.id(), b.id());
        // a different author is a distinct delta (provenance is part of identity).
        let c = Delta::assert("cell-1", b"v".to_vec(), "bob");
        assert_ne!(a.id(), c.id());
        // a different payload is distinct.
        let d = Delta::assert("cell-1", b"w".to_vec(), "alice");
        assert_ne!(a.id(), d.id());
    }

    #[test]
    fn retract_pins_its_target() {
        let a = Delta::assert("cell-1", b"v".to_vec(), "alice");
        let r1 = Delta::retract("cell-1", a.id(), "alice");
        let r2 = Delta::retract("cell-1", [9u8; 32], "alice");
        // a retraction's id depends on exactly what it retracts (Merkle link).
        assert_ne!(r1.id(), r2.id());
    }

    #[test]
    fn no_concatenation_collision_between_fields() {
        // "ab"/"" must not collide with "a"/"b" — the length-prefix guards it.
        let x = Delta::assert("ab", b"".to_vec(), "z");
        let y = Delta::assert("a", b"b".to_vec(), "z");
        assert_ne!(x.id(), y.id());
    }
}
