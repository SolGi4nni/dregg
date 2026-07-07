//! Atoms — the vertices of a [`crate::DocGraph`].
//!
//! An atom is a span of document content with a stable, content-derived
//! identity, an alive/dead status, and **provenance** (who authored it, in which
//! patch). Following Pijul (DOCUMENT-LANGUAGE.md §2.2), an atom is *never
//! physically removed*: a delete only flips its status to [`Status::Dead`] (a
//! tombstone). Because deletion is therefore additive (you add a tombstone, you
//! never subtract a vertex), deletes commute with everything — which is what
//! makes the union-merge total.
//!
//! The provenance is load-bearing for the conflict view (§3.5): each alternative
//! in a conflict carries *who wrote it*, so "who authored which alternative" is a
//! fact, not a guess. It is an [`Author`] + a [`PatchId`] — and under the
//! `cell-heap` ride these exact values are committed state: every structured
//! heap leaf's digest binds them (`substrate::leaf_for_atom` /
//! `leaf_for_field`), and the document's patch chain lives in the cell
//! (`doc_heap`'s `COLL_HISTORY`), so a reopened document replays the same
//! provenance the boundary root committed. The executor-driven ride
//! (`executor_drive`) additionally journals each committed edit as a real turn
//! receipt — a second witness of the same provenance (the receipt↔patch-id
//! cross-check is a named seam, not yet built).

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

/// A stable, content-derived identifier for an atom (a graph vertex).
///
/// A plain 128-bit value that the substrate projection binds VERBATIM: each
/// committed atom leaf's preimage carries this id (`substrate::leaf_for_atom`),
/// and the committed patch chain (`doc_heap`'s `COLL_HISTORY`) re-derives the
/// identical id on replay — so the id a light client's root binds and the id
/// the algebra computes are the same value, not a stand-in for a future one.
/// [`AtomId::ROOT`] is the reserved sentinel that anchors the start of the
/// document — every inserted atom is ordered *after* some existing atom, and
/// the first real atom is ordered after `ROOT`.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct AtomId(pub u128);

impl AtomId {
    /// The sentinel start-of-document vertex. It is always alive and carries no
    /// content; it exists so that "insert at the beginning" is uniformly
    /// "insert after `ROOT`".
    pub const ROOT: AtomId = AtomId(0);

    /// Derive a content-addressed id from an author-chosen seed and the atom's
    /// content. Distinct (seed, content) pairs get distinct ids with
    /// overwhelming probability; identical pairs collide *deliberately* (the
    /// same edit authored twice is the same atom — idempotence).
    ///
    /// The derivation uses `DefaultHasher` — deliberately non-cryptographic.
    /// It supplies the *shape* the patch algebra relies on (deterministic,
    /// content-derived, idempotent); the *commitment's* collision resistance
    /// does not rest on it, because the substrate ride binds the derived id
    /// itself inside a BLAKE3 leaf preimage under the Poseidon2 heap root — a
    /// forged or substituted id cannot hide under the committed boundary.
    pub fn derive(seed: u64, content: &str) -> AtomId {
        let mut h = DefaultHasher::new();
        0xD0Cu64.hash(&mut h);
        seed.hash(&mut h);
        content.hash(&mut h);
        let lo = h.finish();
        let mut h2 = DefaultHasher::new();
        content.hash(&mut h2);
        seed.hash(&mut h2);
        0xA70Du64.hash(&mut h2);
        let hi = h2.finish();
        // Never collide with the ROOT sentinel.
        let v = ((hi as u128) << 64) | (lo as u128);
        AtomId(if v == 0 { 1 } else { v })
    }
}

/// Who authored an edit — an opaque label the conflict view attributes each
/// alternative to. The rides ground it twice: the committed heap binds every
/// `Author` value (inside each provenance-carrying leaf digest AND verbatim in
/// the committed patch chain, `doc_heap`'s `COLL_HISTORY`), and the
/// executor-driven ride (`executor_drive`) realizes the authoring identity as
/// an editor *cell* whose capability gates the edit.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
pub struct Author(pub u64);

impl Author {
    /// The anonymous/system author (e.g. the genesis ROOT atom).
    pub const SYSTEM: Author = Author(0);
}

/// A patch's stable identity — content-addressed over its ops + author, so the
/// same edit has the same id (idempotence at the patch level). The committed
/// patch chain (`doc_heap`'s `COLL_HISTORY`) binds the ops + author this id
/// derives from, so replaying a reopened document re-derives the identical id
/// — blame's patch attribution survives close/reopen. The executor-driven
/// ride's turn receipt is a second, journaled witness of the same edit; the
/// receipt-id↔patch-id correspondence is a named seam, not yet cross-checked.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
pub struct PatchId(pub u128);

impl PatchId {
    /// The genesis "patch" that the ROOT sentinel belongs to.
    pub const GENESIS: PatchId = PatchId(0);
}

/// Provenance carried by every atom: who authored it and in which patch. The
/// document's commitment binds this (a light client cannot be shown an
/// alternative whose author is forged — the conflict-as-state soundness goal of
/// DOCUMENT-LANGUAGE.md §4.4 RESEARCH).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Provenance {
    /// The authoring identity.
    pub author: Author,
    /// The patch that introduced this atom.
    pub patch: PatchId,
}

impl Provenance {
    /// The genesis provenance for the ROOT sentinel.
    pub const GENESIS: Provenance = Provenance {
        author: Author::SYSTEM,
        patch: PatchId::GENESIS,
    };
}

/// The liveness status of an atom. Monotone: an atom may only travel
/// `Alive -> Dead`, never back. The join (used by [`crate::merge`]) is therefore
/// "dead wins" — if either branch tombstoned the atom, the merged atom is dead.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Status {
    /// The atom is live: it participates in the rendered content.
    Alive,
    /// The atom is tombstoned: it is retained in the graph (for provenance and
    /// commutation) but excluded from the rendered content.
    Dead,
}

impl Status {
    /// The monotone join of two statuses: `Dead` absorbs `Alive`.
    pub fn join(self, other: Status) -> Status {
        match (self, other) {
            (Status::Alive, Status::Alive) => Status::Alive,
            _ => Status::Dead,
        }
    }
}

/// A vertex of the document graph: a content span with identity, status, and
/// provenance.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Atom {
    /// The atom's stable identity.
    pub id: AtomId,
    /// The atom's content span (coarse-grained by default — DOCUMENT-LANGUAGE.md
    /// §4.4 leaves the atom granularity an empirical design choice).
    pub content: String,
    /// Alive or tombstoned.
    pub status: Status,
    /// Who authored this atom and in which patch.
    pub provenance: Provenance,
}

impl Atom {
    /// True iff this atom currently participates in the rendered content.
    pub fn is_alive(&self) -> bool {
        self.status == Status::Alive
    }
}
