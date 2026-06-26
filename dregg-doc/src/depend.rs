//! The Pijul **theory of patches** made operational: patch *dependencies*,
//! *unrecord* (pull a patch — and only what truly depends on it — out of the
//! middle of history), *cherry-pick* (grab one patch with its missing deps onto
//! another branch), and *commute* (the independence test).
//!
//! This is the heart of Pijul's identity (DOCUMENT-LANGUAGE.md §4.1, the
//! patch-theory face). Patches **commute** when they are independent — they
//! touch disjoint parts of the graph and neither references atoms the other
//! introduced — and a patch can be pulled out of the middle of a history *as
//! long as you respect its dependents*: every patch that (transitively) builds
//! on it must come out with it, or the replay would dangle.
//!
//! ## What "depends on" means here
//!
//! A patch `P` **depends on** patch `Q` when one of `P`'s ops references an
//! atom (or a field history) that `Q` introduced:
//!
//! - [`Op::Add`]`{ after, .. }` depends on whichever patch introduced `after`.
//!   `after == `[`AtomId::ROOT`] anchors at the document start and depends on
//!   nothing.
//! - [`Op::Connect`]`{ from, to }` depends on the patches introducing `from`
//!   and `to` (each non-`ROOT`).
//! - [`Op::Delete`]`{ id }` (and [`Op::Resurrect`]) depends on the patch
//!   introducing `id`.
//! - A *fresh* [`Op::SetField`] (`superseding == false`) is self-contained and
//!   depends on nothing structural. A *superseding* `SetField` is a resolution
//!   of a prior clash, so it depends on every earlier patch that assigned the
//!   same field name.
//! - The inverse edge ops ([`Op::Disconnect`], [`Op::RetractField`]) carry no
//!   forward dependency (they appear only in inverse patches).
//!
//! An atom is "introduced" by the *first* patch in the history whose `Add`
//! emits it (content-addressing makes a re-add idempotent, so the earliest
//! wins). Dependencies are computed *within a history* — a patch can only
//! depend on a patch that precedes it.

use crate::atom::{AtomId, PatchId};
use crate::history::History;
use crate::patch::{Op, Patch};
use std::collections::{BTreeMap, BTreeSet, VecDeque};

/// Why a [`cherry_pick`] could not be completed.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum DepError {
    /// The requested patch id is not present in the source history.
    NotInSource(PatchId),
    /// A (transitive) dependency of the requested patch references an atom that
    /// no patch in the source history introduces — the patch is not
    /// self-contained relative to the source, so it cannot be replayed cleanly.
    UnsatisfiableDep {
        /// The patch we could not satisfy.
        patch: PatchId,
        /// The dangling atom it references but nothing in the source introduces.
        missing_atom: AtomId,
    },
}

impl std::fmt::Display for DepError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DepError::NotInSource(p) => write!(f, "patch {p:?} not in source history"),
            DepError::UnsatisfiableDep {
                patch,
                missing_atom,
            } => write!(
                f,
                "patch {patch:?} depends on atom {missing_atom:?} which no source patch introduces"
            ),
        }
    }
}

impl std::error::Error for DepError {}

/// Index every atom id to the [`PatchId`] of the *first* patch in `history`
/// that introduces it (via an [`Op::Add`]). The [`AtomId::ROOT`] sentinel maps
/// to [`PatchId::GENESIS`] — it predates every patch.
fn atom_origins(history: &History) -> BTreeMap<AtomId, PatchId> {
    let mut origin = BTreeMap::new();
    origin.insert(AtomId::ROOT, PatchId::GENESIS);
    for p in history.patches() {
        let pid = p.id();
        for op in &p.ops {
            if let Op::Add { id, .. } = op {
                // First introducer wins (content-addressing => idempotent re-add).
                origin.entry(*id).or_insert(pid);
            }
        }
    }
    origin
}

/// The atom ids a single op references as *structural inputs* (the atoms it
/// reads / orders against, NOT the fresh atom an `Add` introduces). `ROOT` is
/// excluded — it depends on nothing.
fn referenced_atoms(op: &Op) -> Vec<AtomId> {
    let mut v = Vec::new();
    let mut push = |a: AtomId| {
        if a != AtomId::ROOT {
            v.push(a);
        }
    };
    match op {
        Op::Add { after, .. } => push(*after),
        Op::Connect { from, to } => {
            push(*from);
            push(*to);
        }
        Op::Delete { id } | Op::Resurrect { id } => push(*id),
        Op::Disconnect { from, to } => {
            push(*from);
            push(*to);
        }
        Op::SetField { .. } | Op::RetractField { .. } => {}
    }
    v
}

/// A precomputed dependency index over a [`History`]: every patch's id (computed
/// once — `Patch::id()` is a double-hash over all ops, so recomputing it inside
/// the O(n²) dependency loops below was the dominant cost) and the atom-origin
/// map. Built once, then every `direct_deps`/`transitive`/`dependents`/`commute`
/// query reads off it instead of re-hashing the whole history per call.
struct DepIndex<'h> {
    history: &'h History,
    /// `ids[i]` is `history.patches()[i].id()` (computed exactly once).
    ids: Vec<PatchId>,
    origin: BTreeMap<AtomId, PatchId>,
}

impl<'h> DepIndex<'h> {
    fn new(history: &'h History) -> Self {
        let ids: Vec<PatchId> = history.patches().iter().map(Patch::id).collect();
        let mut origin = BTreeMap::new();
        origin.insert(AtomId::ROOT, PatchId::GENESIS);
        for (i, p) in history.patches().iter().enumerate() {
            let pid = ids[i];
            for op in &p.ops {
                if let Op::Add { id, .. } = op {
                    origin.entry(*id).or_insert(pid);
                }
            }
        }
        DepIndex {
            history,
            ids,
            origin,
        }
    }

    /// The index (into `history.patches()`/`ids`) of the patch with id `p`.
    fn index_of(&self, p: PatchId) -> Option<usize> {
        self.ids.iter().position(|&id| id == p)
    }

    /// Direct deps of the patch at slot `pi` (id `p == self.ids[pi]`).
    fn direct_deps(&self, pi: usize) -> BTreeSet<PatchId> {
        let p = self.ids[pi];
        let patch = &self.history.patches()[pi];
        let mut deps = BTreeSet::new();
        for op in &patch.ops {
            for atom in referenced_atoms(op) {
                if let Some(&q) = self.origin.get(&atom)
                    && q != PatchId::GENESIS
                    && q != p
                {
                    deps.insert(q);
                }
            }
            if let Op::SetField {
                name,
                superseding: true,
                ..
            } = op
            {
                // Prior writers of `name`: every patch before slot `pi` whose ops
                // touch this field. Uses the precomputed ids (no re-hashing).
                for (j, q) in self.history.patches().iter().enumerate() {
                    if j >= pi {
                        break;
                    }
                    let qid = self.ids[j];
                    if qid != p
                        && q.ops
                            .iter()
                            .any(|op| matches!(op, Op::SetField { name: n, .. } if n == name))
                    {
                        deps.insert(qid);
                    }
                }
            }
        }
        deps
    }

    /// Transitive dependency closure of the patch at slot `pi`. Excludes `p`.
    fn transitive(&self, pi: usize) -> BTreeSet<PatchId> {
        let p = self.ids[pi];
        let mut seen = BTreeSet::new();
        let mut queue: VecDeque<PatchId> = self.direct_deps(pi).into_iter().collect();
        while let Some(q) = queue.pop_front() {
            if seen.insert(q) {
                if let Some(qi) = self.index_of(q) {
                    for r in self.direct_deps(qi) {
                        if !seen.contains(&r) {
                            queue.push_back(r);
                        }
                    }
                }
            }
        }
        seen.remove(&p);
        seen
    }
}

/// The **direct** dependencies of patch `p` within `history`: scan `p`'s ops,
/// and for every referenced atom find the patch that introduced it; for every
/// superseding field write, the prior writers of that field. A patch never
/// depends on itself or on [`PatchId::GENESIS`] (the ROOT anchor).
///
/// If `p` is not in the history, returns an empty set.
pub fn dependencies(history: &History, p: PatchId) -> BTreeSet<PatchId> {
    let idx = DepIndex::new(history);
    match idx.index_of(p) {
        Some(pi) => idx.direct_deps(pi),
        None => BTreeSet::new(),
    }
}

/// The **transitive** dependency closure of `p` (every patch `p` rests on,
/// directly or indirectly). Excludes `p` itself.
pub fn transitive_dependencies(history: &History, p: PatchId) -> BTreeSet<PatchId> {
    let idx = DepIndex::new(history);
    match idx.index_of(p) {
        Some(pi) => idx.transitive(pi),
        None => BTreeSet::new(),
    }
}

/// The **dependents** of `p`: every patch in `history` that (transitively)
/// depends on `p`. These are exactly the patches that must come out *with* `p`
/// if it is unrecorded — pulling `p` while leaving a dependent behind would
/// dangle the dependent's references. Excludes `p` itself.
pub fn dependents(history: &History, p: PatchId) -> BTreeSet<PatchId> {
    let idx = DepIndex::new(history);
    let mut out = BTreeSet::new();
    for qi in 0..idx.ids.len() {
        let qid = idx.ids[qi];
        if qid == p {
            continue;
        }
        if idx.transitive(qi).contains(&p) {
            out.insert(qid);
        }
    }
    out
}

/// `true` iff `p` and `q` are **independent** — neither (transitively) depends
/// on the other, so they commute (can be reordered without changing the replay).
/// A patch trivially commutes with itself's-absence; `p == q` returns `false`
/// (a patch does not commute *past* itself). Patches not in the history are
/// treated as having no dependency relation (vacuously independent).
pub fn commute(history: &History, p: PatchId, q: PatchId) -> bool {
    if p == q {
        return false;
    }
    let idx = DepIndex::new(history);
    let p_deps = idx
        .index_of(p)
        .map(|pi| idx.transitive(pi))
        .unwrap_or_default();
    if p_deps.contains(&q) {
        return false;
    }
    let q_deps = idx
        .index_of(q)
        .map(|qi| idx.transitive(qi))
        .unwrap_or_default();
    !q_deps.contains(&p)
}

/// **Unrecord** patch `p`: return a NEW history with `p` and *all its transitive
/// dependents* removed, preserving the order of the remaining (independent)
/// patches. This is "pull this feature out, keep everything that doesn't rest on
/// it." The result's [`History::replay`] is always a valid [`DocGraph`] with no
/// dangling references, *because* the dependents come out too.
///
/// If `p` is not in the history, returns a clone unchanged.
pub fn unrecord(history: &History, p: PatchId) -> History {
    let mut remove = dependents(history, p);
    remove.insert(p);
    let mut out = History::new();
    for q in history.patches() {
        if !remove.contains(&q.id()) {
            out.commit(q.clone());
        }
    }
    out
}

/// **Cherry-pick** patch `p` from `source` onto `onto`: apply `p` together with
/// any of its transitive dependencies that `onto` is missing, in dependency
/// order (deps before dependents). This is "grab just this one fix from another
/// branch." Patches already present in `onto` are skipped (idempotent).
///
/// Returns the [`PatchId`] of the cherry-picked patch on success.
///
/// Errors:
/// - [`DepError::NotInSource`] if `p` is not in `source`.
/// - [`DepError::UnsatisfiableDep`] if `p` (or a dep) references an atom that no
///   `source` patch introduces and that `onto` does not already have — the patch
///   is not self-contained, so replaying it would dangle.
pub fn cherry_pick(source: &History, p: PatchId, onto: &mut History) -> Result<PatchId, DepError> {
    if !source.patches().iter().any(|q| q.id() == p) {
        return Err(DepError::NotInSource(p));
    }

    // Atoms already realized in `onto` (so an `after` anchor it owns is fine).
    let onto_have: BTreeSet<PatchId> = onto.patches().iter().map(Patch::id).collect();
    let onto_atoms: BTreeSet<AtomId> = {
        let mut s = BTreeSet::new();
        s.insert(AtomId::ROOT);
        for q in onto.patches() {
            for op in &q.ops {
                if let Op::Add { id, .. } = op {
                    s.insert(*id);
                }
            }
        }
        s
    };

    let source_origin = atom_origins(source);

    // The patches we must bring over: p plus its source-side transitive deps,
    // minus what `onto` already has.
    let mut needed: BTreeSet<PatchId> = transitive_dependencies(source, p);
    needed.insert(p);
    needed.retain(|q| !onto_have.contains(q));

    // Verify self-containment: every atom a needed patch references must be
    // introducible — by some source patch, or already present in `onto`.
    for q in source.patches() {
        let qid = q.id();
        if !needed.contains(&qid) {
            continue;
        }
        for op in &q.ops {
            for atom in referenced_atoms(op) {
                let from_source = source_origin
                    .get(&atom)
                    .is_some_and(|o| *o != PatchId::GENESIS);
                if !from_source && !onto_atoms.contains(&atom) {
                    return Err(DepError::UnsatisfiableDep {
                        patch: qid,
                        missing_atom: atom,
                    });
                }
            }
        }
    }

    // Apply the needed patches in source order (which is a valid topological
    // order: deps always precede dependents in a well-formed history).
    for q in source.patches() {
        if needed.contains(&q.id()) {
            onto.commit(q.clone());
        }
    }
    Ok(p)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::atom::Author;
    use crate::content;

    /// Build the canonical scenario:
    ///   patch1: add "A" after ROOT
    ///   patch2: add "B" after A   (depends on patch1)
    ///   patch3: add "C" after ROOT (independent)
    /// Returns (history, id1, id2, id3, atomA, atomB, atomC).
    fn scenario() -> (History, PatchId, PatchId, PatchId, AtomId, AtomId, AtomId) {
        let mut h = History::new();
        let (a, op_a) = Patch::add(1, "A", AtomId::ROOT);
        let (b, op_b) = Patch::add(2, "B", a);
        let (c, op_c) = Patch::add(3, "C", AtomId::ROOT);
        let id1 = h.commit(Patch::by(Author(1), [op_a]));
        let id2 = h.commit(Patch::by(Author(1), [op_b]));
        let id3 = h.commit(Patch::by(Author(1), [op_c]));
        (h, id1, id2, id3, a, b, c)
    }

    #[test]
    fn direct_dependencies_follow_after_anchor() {
        let (h, id1, id2, id3, _, _, _) = scenario();
        // patch2 ("B" after A) depends on patch1 (which introduced A).
        assert_eq!(dependencies(&h, id2), BTreeSet::from([id1]));
        // patch1 ("A" after ROOT) depends on nothing.
        assert!(dependencies(&h, id1).is_empty());
        // patch3 ("C" after ROOT) depends on nothing.
        assert!(dependencies(&h, id3).is_empty());
    }

    #[test]
    fn independent_patches_commute_dependent_ones_do_not() {
        let (h, id1, id2, id3) = {
            let (h, id1, id2, id3, ..) = scenario();
            (h, id1, id2, id3)
        };
        // patch2 and patch3 are independent => commute.
        assert!(commute(&h, id2, id3));
        assert!(commute(&h, id3, id2));
        // patch1 and patch2 are NOT independent (patch2 depends on patch1).
        assert!(!commute(&h, id1, id2));
        assert!(!commute(&h, id2, id1));
        // A patch does not commute past itself.
        assert!(!commute(&h, id1, id1));
    }

    #[test]
    fn dependents_are_the_reverse_relation() {
        let (h, id1, id2, _id3, ..) = scenario();
        // patch2 depends on patch1, so patch1's dependents include patch2.
        assert_eq!(dependents(&h, id1), BTreeSet::from([id2]));
        // patch2 has no dependents.
        assert!(dependents(&h, id2).is_empty());
    }

    #[test]
    fn unrecord_removes_dependents_keeps_independent() {
        let (h, id1, _id2, _id3, _, _, _) = scenario();
        // Pull patch1 ("A"): patch2 ("B" after A) must come out too (dependent),
        // but patch3 ("C") is independent and stays.
        let pulled = unrecord(&h, id1);
        let g = pulled.replay();
        // Only "C" survives; no dangling "B".
        assert_eq!(content(&g).to_marked_string(), "C");
        // The history has exactly one patch left (patch3).
        assert_eq!(pulled.len(), 1);
    }

    #[test]
    fn unrecord_independent_patch_removes_only_it() {
        let (h, _id1, _id2, id3, _, _, _) = scenario();
        // patch3 ("C") is independent: pulling it leaves "AB".
        let pulled = unrecord(&h, id3);
        let g = pulled.replay();
        assert_eq!(content(&g).to_marked_string(), "AB");
        assert_eq!(pulled.len(), 2);
    }

    #[test]
    fn unrecord_replay_has_no_dangling_edges() {
        // Even with a longer dependent chain, unrecord keeps replay valid.
        let mut h = History::new();
        let (a, op_a) = Patch::add(1, "A", AtomId::ROOT);
        let (b, op_b) = Patch::add(2, "B", a);
        let (_c, op_c) = Patch::add(3, "C", b); // C after B after A — a chain
        let id1 = h.commit(Patch::by(Author(1), [op_a]));
        let _ = h.commit(Patch::by(Author(1), [op_b]));
        let _ = h.commit(Patch::by(Author(1), [op_c]));
        let pulled = unrecord(&h, id1);
        // The whole chain comes out; replay is the empty document.
        assert_eq!(pulled.len(), 0);
        assert_eq!(content(&pulled.replay()).to_marked_string(), "");
    }

    #[test]
    fn commutation_law_independent_patches_commute_on_the_graph() {
        // The Pijul law: independent patches commute structurally.
        // base: a one-atom doc "X".
        let mut base = crate::DocGraph::new();
        let (x, op_x) = Patch::add(9, "X", AtomId::ROOT);
        Patch::by(Author(1), [op_x]).apply(&mut base);

        // p inserts "P" after X; q inserts "Q" after X — independent of each
        // other (neither references the other's atom).
        let p = Patch::by(Author(1), [Patch::add(10, "P", x).1]);
        let q = Patch::by(Author(2), [Patch::add(11, "Q", x).1]);

        let pq = q.apply_to(&p.apply_to(&base));
        let qp = p.apply_to(&q.apply_to(&base));
        assert!(
            pq.structural_eq(&qp),
            "independent patches must commute on the graph"
        );
    }

    #[test]
    fn cherry_pick_pulls_missing_dependency_first() {
        let (src, _id1, id2, _id3, _, _, _) = scenario();
        // Pull patch2 ("B" after A) onto a fresh history: it must auto-pull
        // patch1 (its dep) first.
        let mut onto = History::new();
        let picked = cherry_pick(&src, id2, &mut onto).expect("cherry-pick patch2");
        assert_eq!(picked, id2);
        // Both patch1 and patch2 landed (2 patches), in dependency order.
        assert_eq!(onto.len(), 2);
        // Replay shows "AB" — the dep was satisfied.
        assert_eq!(content(&onto.replay()).to_marked_string(), "AB");
    }

    #[test]
    fn cherry_pick_standalone_patch_succeeds_alone() {
        let (src, _id1, _id2, id3, _, _, _) = scenario();
        let mut onto = History::new();
        let picked = cherry_pick(&src, id3, &mut onto).expect("cherry-pick patch3");
        assert_eq!(picked, id3);
        // patch3 ("C" after ROOT) is self-contained: it lands alone.
        assert_eq!(onto.len(), 1);
        assert_eq!(content(&onto.replay()).to_marked_string(), "C");
    }

    #[test]
    fn cherry_pick_is_idempotent_against_existing() {
        let (src, id1, id2, _id3, _, _, _) = scenario();
        let mut onto = History::new();
        // onto already has patch1.
        cherry_pick(&src, id1, &mut onto).unwrap();
        assert_eq!(onto.len(), 1);
        // Picking patch2 now only adds patch2 (patch1 already present).
        cherry_pick(&src, id2, &mut onto).unwrap();
        assert_eq!(onto.len(), 2);
        assert_eq!(content(&onto.replay()).to_marked_string(), "AB");
    }

    #[test]
    fn cherry_pick_not_in_source_errors() {
        let (src, ..) = scenario();
        let mut onto = History::new();
        let bogus = PatchId(0xDEAD_BEEF);
        assert_eq!(
            cherry_pick(&src, bogus, &mut onto),
            Err(DepError::NotInSource(bogus))
        );
    }

    #[test]
    fn transitive_dependencies_chase_the_chain() {
        let mut h = History::new();
        let (a, op_a) = Patch::add(1, "A", AtomId::ROOT);
        let (b, op_b) = Patch::add(2, "B", a);
        let (_c, op_c) = Patch::add(3, "C", b);
        let id1 = h.commit(Patch::by(Author(1), [op_a]));
        let id2 = h.commit(Patch::by(Author(1), [op_b]));
        let id3 = h.commit(Patch::by(Author(1), [op_c]));
        // patch3 directly depends on patch2; transitively also on patch1.
        assert_eq!(dependencies(&h, id3), BTreeSet::from([id2]));
        assert_eq!(transitive_dependencies(&h, id3), BTreeSet::from([id1, id2]));
    }

    #[test]
    fn superseding_setfield_depends_on_prior_writers() {
        // Two concurrent fresh assigns to "title", then a superseding resolve.
        let mut h = History::new();
        let p1 = Patch::by(
            Author(1),
            [Op::SetField {
                name: "title".into(),
                value: "Alpha".into(),
                superseding: false,
            }],
        );
        let p2 = Patch::by(
            Author(2),
            [Op::SetField {
                name: "title".into(),
                value: "Beta".into(),
                superseding: false,
            }],
        );
        let resolve = Patch::by(
            Author(1),
            [Op::SetField {
                name: "title".into(),
                value: "Alpha".into(),
                superseding: true,
            }],
        );
        let id1 = h.commit(p1);
        let id2 = h.commit(p2);
        let id3 = h.commit(resolve);
        // The fresh assigns depend on nothing structural.
        assert!(dependencies(&h, id1).is_empty());
        assert!(dependencies(&h, id2).is_empty());
        // The superseding resolve depends on BOTH prior writers (the clash it
        // settles) — you cannot pull a resolution while keeping the clash dangling.
        assert_eq!(dependencies(&h, id3), BTreeSet::from([id1, id2]));
        // The two fresh assigns are independent => commute.
        assert!(commute(&h, id1, id2));
    }
}
