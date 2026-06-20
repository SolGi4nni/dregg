//! # dregg-doc — the Pijul-shaped patch-theory core for the dreggverse document language
//!
//! A dreggverse hypermedia document is a *patch-theoretic object*: a document is
//! a **graph of alive/dead content atoms** with order-edges; an edit is a
//! **patch** (`Add` / `Delete`(tombstone) / `Connect`); two concurrent edits are
//! reconciled by **merge**, the categorical **pushout** computed as a total
//! graph union; and a **conflict** — two live, mutually-unordered alternatives
//! at one position — is a *first-class STATE* the document carries until a later
//! patch resolves it, **never a merge failure**.
//!
//! This is the math of Mimram–Di Giusto's *A Categorical Theory of Patches*
//! (repositories = objects, patches = morphisms, merge = pushout) realized in
//! Pijul's concrete graph-of-atoms model. The companion spec is
//! `docs/deos/DOCUMENT-LANGUAGE.md`.
//!
//! ## The shape
//!
//! - [`DocGraph`] — the graph of atoms ([`Atom`]: an [`AtomId`], content, an
//!   alive/dead [`Status`], and [`Provenance`]) plus order-edges, *plus* the
//!   single-valued field store (the non-monotone fragment).
//! - [`Patch`] — the authored grammar ([`Op::Add`] / [`Op::Delete`] /
//!   [`Op::Connect`] / [`Op::SetField`]) with [`Patch::apply`],
//!   [`Patch::compose`], and [`Patch::invert`] (RCCS reversibility).
//! - [`History`] — a document *as* its patch-history; content is
//!   [`History::replay`] / [`History::replay_to`] (time-travel), and
//!   [`History::branch`] / [`History::stitch`] are the branch-and-stitch faces.
//! - [`dependencies`] / [`transitive_dependencies`] / [`dependents`] /
//!   [`commute`] / [`unrecord`] / [`cherry_pick`] — the **theory of patches**:
//!   a patch *depends on* the patches that introduced the atoms it references,
//!   independent patches *commute*, and [`unrecord`] pulls a patch (with only
//!   its transitive dependents) out of the middle of history while [`cherry_pick`]
//!   grabs one patch (with its missing deps) onto another branch.
//! - [`Doc`] — the **ergonomic authoring path**: author by typing TEXT, not by
//!   hand-assembling ops. [`Doc::edit`] diffs the current text against the new
//!   text (token LCS at a [`Granularity`]) and commits the minimal `Add`/`Delete`
//!   patch — kept tokens reuse their existing atom ids; inserted tokens get
//!   predecessor-seeded ids so repeated tokens stay distinct. [`walk_atoms`] is
//!   the per-atom linearization this rides on.
//! - [`merge`] — the pushout/union: total, commutative, associative, idempotent.
//! - [`content`] — the fold/linearization, with conflicts surfaced as
//!   [`ConflictRegion`]s ([`Segment::Conflict`]), each [`Alternative`] tagged
//!   with its [`Provenance`] ("who wrote which alternative" is a fact).
//! - [`blame`] — per-atom authorship that is **correct**: because the
//!   [`AtomId`] is content-addressed and stable, [`blame`] reads authorship off
//!   each live atom's provenance and that attribution does NOT move when the
//!   surrounding text does (the git-blame middle-insert failure cannot occur);
//!   [`blame_summary`] tallies contributions per [`Author`].
//! - [`render_three_way`] — the diff3 / merge-base conflict view: each conflict
//!   region shown with the common-ancestor [`merge_base`] content (the BASE
//!   column) alongside every diverging [`ConflictSide`], so OURS/THEIRS are read
//!   against what they both forked from.
//! - [`Regime`] — the two-regime classifier: a [`Regime::Prose`] antichain
//!   (illusory / unilaterally resolvable) vs a [`Regime::Field`] conservation /
//!   authority clash (a *real* conflict that may need consensus).
//! - [`resolve_connect`] / [`resolve_keep`] / [`resolve_field`] — resolution
//!   patches that collapse a conflict (order / choose / settle a field).
//! - [`commit`] — the document [`Commitment`] that binds atoms, edges, and
//!   field assignments *with their provenance*, so a light client cannot be
//!   shown a conflict that hides or forges an alternative (§4.4 soundness).
//!
//! ## The substrate ride (the `substrate` feature — the REAL commitment)
//!
//! With `--features substrate`, the document rides the REAL dregg cell
//! substrate: [`to_heap_map`] projects a [`DocGraph`] into a production cell
//! heap (`(collection_id, key) -> 32-byte` leaves, atoms/edges/fields in
//! distinct collections, each leaf binding provenance) and [`substrate_commit`]
//! is the sorted-Poseidon2 heap root over it — the faithful commitment a light
//! client actually trusts. This REPLACES the in-crate [`commit`]
//! `DefaultHasher` stand-in with the real ride (DOCUMENT-LANGUAGE.md §4.1), and
//! the anti-forge tooth is re-proven against the real Poseidon2 root.
//!
//! ## What this crate stays (with the feature OFF — "let it breathe")
//!
//! By default this is a STANDALONE, dependency-free core: pure data structures
//! and algorithms, fast and `cargo test`-able in isolation, riding no substrate.
//! The atom granularity, the surface syntax, and the conflict-view UX are left
//! to emerge from authoring real documents on this core (§4.4, §5).
//!
//! ## Example
//!
//! ```
//! use dregg_doc::{DocGraph, History, Patch, Author, AtomId, content, merge};
//!
//! // A document is its patch-history; content is the fold.
//! let mut h = History::new();
//! let (hello, add) = Patch::add(1, "Hello, ", AtomId::ROOT);
//! let (world, add2) = Patch::add(2, "world.", hello);
//! h.commit(Patch::by(Author(1), [add]));
//! h.commit(Patch::by(Author(1), [add2]));
//! assert_eq!(content(&h.replay()).to_marked_string(), "Hello, world.");
//!
//! // Two authors append concurrently at the tail => a first-class conflict
//! // (not a failure), each alternative tagged with who wrote it.
//! let base = h.replay();
//! let a = Patch::by(Author(1), [Patch::add(3, " A", world).1]).apply_to(&base);
//! let b = Patch::by(Author(2), [Patch::add(4, " B", world).1]).apply_to(&base);
//! let merged = merge(&a, &b);
//! let r = content(&merged);
//! assert!(r.has_conflict());
//! // "world." is still clean; the rest of the doc is fully usable.
//! assert!(r.to_marked_string().starts_with("Hello, world."));
//! ```

mod atom;
mod blame;
mod commit;
mod content;
mod depend;
mod doc;
mod graph;
mod history;
mod merge;
mod patch;
mod regime;
mod resolve;
mod threeway;
#[cfg(feature = "substrate")]
mod substrate;
#[cfg(feature = "substrate")]
mod doccell;
#[cfg(feature = "substrate")]
mod executor_drive;

pub use atom::{Atom, AtomId, Author, PatchId, Provenance, Status};
pub use blame::{BlameLine, blame, blame_summary};
pub use commit::{Commitment, commit};
pub use depend::{
    DepError, cherry_pick, commute, dependencies, dependents, transitive_dependencies, unrecord,
};
#[cfg(feature = "substrate")]
pub use substrate::{COLL_ATOMS, COLL_EDGES, COLL_FIELDS, substrate_commit, to_heap_map};
#[cfg(feature = "substrate")]
pub use doccell::{DocCell, decode_index, desugar_op_kind, encode_index, project_graph};
#[cfg(feature = "substrate")]
pub use executor_drive::{ExecutorDrivenDoc, field_key};
pub use content::{Alternative, ConflictRegion, Rendered, Segment, content, walk_atoms};
pub use doc::{Doc, Granularity};
pub use graph::{DocGraph, FieldAssign};
pub use history::History;
pub use merge::{merge, merge_all};
pub use patch::{Op, Patch};
pub use regime::Regime;
pub use resolve::{
    resolve_connect, resolve_connect_by, resolve_field, resolve_keep, resolve_keep_by,
};
pub use threeway::{
    ConflictSide, ThreeWayConflict, merge_base, render_three_way, three_way,
};

#[cfg(test)]
mod tests;
