//! The document commitment — binding the whole document, *including conflict
//! provenance*, so a light client cannot be shown a forged conflict.
//!
//! `DOCUMENT-LANGUAGE.md` §4.4 RESEARCH (conflict-as-state soundness): a stored
//! conflict state must bind, in the document's commitment, **both** live
//! alternatives *and their provenance*, so a light client cannot be shown a
//! conflict that hides or forges an alternative. This module is that binding.
//!
//! [`commit`] folds the document's canonical form — the sorted atoms (id +
//! content + status + **provenance**), the sorted order-edges, and the sorted
//! field assignments (value + **provenance**) — into a [`Commitment`]. The
//! canonical order is free: [`crate::DocGraph`] stores everything in
//! `BTreeMap`/`BTreeSet`, so iteration is deterministic and construction-order
//! independent. Every variable-length run is **length-prefixed** so a field can
//! never be confused for an atom (no concatenation-ambiguity collision), and a
//! domain tag separates this from any other hash in the system.
//!
//! The anti-forge tooth: because provenance is *inside* the preimage, mutating
//! one conflict alternative's author — even while its rendered text is
//! unchanged — changes the commitment. You cannot show a light client a
//! conflict whose alternatives render identically but whose authorship is
//! forged or dropped (see the `commit` tests).
//!
//! NOTE (the honest stand-in): [`commit`] uses the crate's double-`DefaultHasher`
//! 128-bit content-addressing, the same as [`crate::AtomId::derive`] /
//! `Patch::id`. `DefaultHasher` is **not** cryptographic — it is the in-crate
//! stand-in that lets the soundness *property* be tested. The real substrate
//! commitment is sorted-Poseidon2 over the document cell's heap (the faithful
//! 8-felt commitment floor); this crate rides that later (§4.1).

use crate::atom::{Provenance, Status};
use crate::graph::DocGraph;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

/// A document's commitment: a 128-bit digest over its canonical form, binding
/// atoms, order-edges, and field assignments **with their provenance**. Two
/// fully-equal documents (atoms, edges, fields, *and* provenance) commit equal;
/// any change — including a forged/dropped conflict alternative's provenance —
/// changes the commitment.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Commitment(pub u128);

/// The domain tag separating this commitment from every other hash in the system.
const DOMAIN: &[u8] = b"dregg-doc/commit/v1";

/// A canonical, length-prefixed byte encoder feeding the digest. Length-prefixes
/// every variable-length run so sections cannot be confused (the
/// anti-concatenation-ambiguity discipline).
struct Encoder {
    bytes: Vec<u8>,
}

impl Encoder {
    fn new() -> Self {
        let mut e = Encoder { bytes: Vec::new() };
        e.tag(DOMAIN);
        e
    }

    /// A fixed domain/section tag (length-prefixed).
    fn tag(&mut self, t: &[u8]) {
        self.bytes
            .extend_from_slice(&(t.len() as u64).to_le_bytes());
        self.bytes.extend_from_slice(t);
    }

    /// A fixed-width u128.
    fn u128(&mut self, v: u128) {
        self.bytes.extend_from_slice(&v.to_le_bytes());
    }

    /// A fixed-width u64.
    fn u64(&mut self, v: u64) {
        self.bytes.extend_from_slice(&v.to_le_bytes());
    }

    /// A length-prefixed byte run (e.g. content / field name / value).
    fn bytes_run(&mut self, b: &[u8]) {
        self.bytes
            .extend_from_slice(&(b.len() as u64).to_le_bytes());
        self.bytes.extend_from_slice(b);
    }

    /// One status byte.
    fn status(&mut self, s: Status) {
        self.bytes.push(match s {
            Status::Alive => 0,
            Status::Dead => 1,
        });
    }

    /// Provenance: author then patch id (both fixed-width). This is the binding
    /// that makes the anti-forge tooth bite.
    fn provenance(&mut self, p: Provenance) {
        self.u64(p.author.0);
        self.u128(p.patch.0);
    }

    /// Finalize into a 128-bit commitment via the crate's double-hash idiom.
    fn finish(self) -> Commitment {
        let mut h = DefaultHasher::new();
        self.bytes.hash(&mut h);
        let lo = h.finish();
        let mut h2 = DefaultHasher::new();
        0xC0_3317u64.hash(&mut h2);
        self.bytes.hash(&mut h2);
        let hi = h2.finish();
        Commitment(((hi as u128) << 64) | (lo as u128))
    }
}

/// Commit a document: fold its canonical form into a [`Commitment`] that binds
/// atoms, order-edges, and field assignments with their provenance.
///
/// The sections, each length-prefixed and tagged:
/// 1. **atoms**, in id order: id ‖ content ‖ status ‖ provenance;
/// 2. **edges**, in (from, to) order: from ‖ successors;
/// 3. **fields**, in name order: name ‖ assignments (value ‖ provenance).
pub fn commit(g: &DocGraph) -> Commitment {
    let mut e = Encoder::new();

    // 1. Atoms (BTreeMap id-order is canonical). Provenance is bound here.
    e.tag(b"atoms");
    e.u64(g.atom_count() as u64);
    for a in g.atoms() {
        e.u128(a.id.0);
        e.bytes_run(a.content.as_bytes());
        e.status(a.status);
        e.provenance(a.provenance);
    }

    // 2. Order-edges (from-id order; successors already BTreeSet-sorted).
    e.tag(b"edges");
    for from in g.atoms().map(|a| a.id) {
        let mut succ = g.successors(from).peekable();
        if succ.peek().is_none() {
            continue;
        }
        // The successor count is needed up-front (length-prefix); the set is
        // BTreeSet-sorted, so collecting once preserves the canonical order.
        let succ: Vec<_> = succ.collect();
        e.u128(from.0);
        e.u64(succ.len() as u64);
        for to in succ {
            e.u128(to.0);
        }
    }

    // 3. Field assignments (name order; assignments value-then-patch sorted).
    //    Both clashing alternatives' provenance is bound here.
    e.tag(b"fields");
    let names: Vec<String> = g.field_names().map(|s| s.to_string()).collect();
    e.u64(names.len() as u64);
    for name in names {
        e.bytes_run(name.as_bytes());
        let assigns = g.field(&name);
        e.u64(assigns.len() as u64);
        for a in assigns {
            e.bytes_run(a.value.as_bytes());
            e.provenance(a.provenance);
        }
    }

    e.finish()
}
