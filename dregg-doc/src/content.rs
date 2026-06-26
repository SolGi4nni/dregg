//! Linearization — folding the graph into rendered content, with conflicts
//! surfaced as first-class regions (carrying provenance).
//!
//! The visible document is a topological walk over the *alive* atoms following
//! the order-edges (DOCUMENT-LANGUAGE.md §2.2-2.3). Where the walk reaches a
//! position with **two or more live successors and no order-edge among them** —
//! a genuine *antichain* in the order — it cannot linearize them, because the
//! order genuinely is not in the graph. That fork is a [`ConflictRegion`] of
//! [`Regime::Prose`]: a first-class STATE, surfaced (never a panic, never a
//! failure), each alternative tagged with **who authored it** (§3.5), carried
//! until a later resolution patch collapses the antichain.
//!
//! Single-valued **field** clashes (§2.4) surface as [`Regime::Field`] conflict
//! regions too — the non-monotone boundary where consensus may be required.

use crate::atom::{AtomId, Provenance};
use crate::graph::DocGraph;
use crate::regime::Regime;
use std::collections::BTreeSet;

/// One live alternative within a conflict: its addressable head/field handle,
/// its rendered text, and its provenance (who wrote it — a *fact*, §3.5).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Alternative {
    /// For a prose conflict: the fork-point atom id a resolution patch
    /// `Connect`s or `Delete`s. For a field conflict: unused ([`AtomId::ROOT`]).
    pub head: AtomId,
    /// The rendered content / field value of this alternative.
    pub text: String,
    /// Who authored this alternative.
    pub provenance: Provenance,
}

/// One unit of rendered output.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Segment {
    /// A clean run of content with a unique order — the common case.
    Clean(String),
    /// A conflicted region: two-or-more live, mutually-unordered (or
    /// single-valued-clashing) alternatives at one position. A first-class
    /// state, resolved by a later patch — *not* an error.
    Conflict(ConflictRegion),
}

/// A first-class conflict: an antichain of two-or-more live alternatives (prose)
/// or a multi-valued field clash. The document carries this state (it is part of
/// a valid rendered document) until a resolution patch collapses it. Each
/// alternative carries its provenance, so the conflict view can attribute "who
/// wrote which alternative" as a fact.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ConflictRegion {
    /// Which regime this conflict belongs to — the answer to "is this real?".
    pub regime: Regime,
    /// For a field clash, the field name; for a prose antichain, `None`.
    pub field: Option<String>,
    /// The live alternatives, sorted canonically.
    pub alternatives: Vec<Alternative>,
}

impl ConflictRegion {
    /// The fork-point heads (for a prose conflict, the addressable atom ids).
    pub fn heads(&self) -> Vec<AtomId> {
        self.alternatives.iter().map(|a| a.head).collect()
    }
}

/// The full rendered content of a document: a sequence of clean runs and
/// conflict regions, in document order, with field conflicts appended.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct Rendered {
    /// The segments in order.
    pub segments: Vec<Segment>,
}

impl Rendered {
    /// True iff the document currently carries at least one unresolved conflict.
    pub fn has_conflict(&self) -> bool {
        self.segments
            .iter()
            .any(|s| matches!(s, Segment::Conflict(_)))
    }

    /// All conflict regions, in document order.
    pub fn conflicts(&self) -> impl Iterator<Item = &ConflictRegion> {
        self.segments.iter().filter_map(|s| match s {
            Segment::Conflict(c) => Some(c),
            Segment::Clean(_) => None,
        })
    }

    /// All prose conflicts.
    pub fn prose_conflicts(&self) -> impl Iterator<Item = &ConflictRegion> {
        self.conflicts().filter(|c| c.regime == Regime::Prose)
    }

    /// All field conflicts.
    pub fn field_conflicts(&self) -> impl Iterator<Item = &ConflictRegion> {
        self.conflicts().filter(|c| c.regime == Regime::Field)
    }

    /// A flat textual rendering for inspection/tests. Clean runs render as their
    /// content; a conflict renders its alternatives (with author) between
    /// markers, so a conflict is *legible* (the AOL-wonder bar: "two people
    /// wrote this differently — here's both") rather than swallowed.
    pub fn to_marked_string(&self) -> String {
        let mut out = String::new();
        for seg in &self.segments {
            match seg {
                Segment::Clean(s) => out.push_str(s),
                Segment::Conflict(c) => {
                    out.push_str("<<<");
                    out.push_str(c.regime.label());
                    if let Some(f) = &c.field {
                        out.push('(');
                        out.push_str(f);
                        out.push(')');
                    }
                    for alt in &c.alternatives {
                        out.push_str("\n|| @");
                        out.push_str(&alt.provenance.author.0.to_string());
                        out.push_str(": ");
                        out.push_str(&alt.text);
                    }
                    out.push_str("\n>>>");
                }
            }
        }
        out
    }
}

/// Walk the *alive* atoms in document order, yielding `(id, content)` for each.
///
/// This is the per-atom companion to [`content`]: where `content` coalesces a
/// clean run into one `String` (losing the atom boundaries), `walk_atoms`
/// preserves the atom granularity so a caller can map "the token at position i"
/// back to "the atom id holding it" — which is exactly what the ergonomic
/// text-diff authoring path ([`crate::Doc`]) needs to MATCH kept tokens to their
/// existing atoms instead of re-minting them.
///
/// It follows the same walk as [`content`]: start at [`AtomId::ROOT`], step
/// through the single live successor, conducting order *through* tombstones. At
/// a genuine antichain (a conflict) the linear order is not in the graph, so the
/// walk stops at the fork (the clean prefix is what's authorable). For a clean
/// linear document — the steady state of single-author text editing — this
/// yields every alive atom in order.
pub fn walk_atoms(g: &DocGraph) -> Vec<(AtomId, String)> {
    let mut out = Vec::new();
    let mut visited = BTreeSet::new();
    let mut cursor = AtomId::ROOT;
    loop {
        let succ = live_successors(g, cursor);
        // Mirror the [`content`] walk's order resolution: a single live successor
        // advances; multiple successors that are actually *ordered* (one
        // reachable from another — the insert-in-the-middle shape, where the
        // anchor keeps its old edge to the successor the insert threads before)
        // collapse to the minimal one; only a genuine antichain (>=2 mutually
        // unreachable) is a conflict with no linear order, where we stop.
        let next = match succ.as_slice() {
            [] => return out,
            [single] => *single,
            many => {
                let antichain: Vec<AtomId> = many
                    .iter()
                    .copied()
                    .filter(|&a| !many.iter().any(|&b| b != a && reachable(g, b, a)))
                    .collect();
                if antichain.len() >= 2 {
                    return out; // a genuine fork: stop at the clean prefix.
                }
                antichain.first().copied().unwrap_or(many[0])
            }
        };
        if !visited.insert(next) {
            return out;
        }
        if let Some(a) = g.atom(next) {
            out.push((next, a.content.clone()));
        }
        cursor = next;
    }
}

/// Linearize a document graph into rendered content, surfacing antichains and
/// field clashes as first-class conflict regions.
///
/// The walk starts at [`AtomId::ROOT`] and follows order-edges through *alive*
/// atoms. At each step we look at the alive successors reachable from the
/// current frontier:
/// - exactly one path forward => emit it as clean content;
/// - two-or-more mutually-unordered alive successors => emit a prose
///   [`ConflictRegion`], then end the walk at the fork.
///
/// Dead atoms are skipped for content but still conduct order (you can walk
/// *through* a tombstone to its successors), which is what makes a delete
/// monotone and order-preserving. Field clashes are appended after the prose
/// walk.
pub fn content(g: &DocGraph) -> Rendered {
    let mut out = Rendered::default();
    let mut visited = BTreeSet::new();
    walk(g, AtomId::ROOT, &mut visited, &mut out.segments);
    coalesce(&mut out.segments);
    append_field_conflicts(g, &mut out.segments);
    out
}

/// Live successors of `id`, walking *through* tombstones (a dead atom conducts
/// order but contributes no content). Returns alive atom ids, deduped + sorted.
fn live_successors(g: &DocGraph, id: AtomId) -> Vec<AtomId> {
    let mut seen = BTreeSet::new();
    let mut out = BTreeSet::new();
    let mut stack: Vec<AtomId> = g.successors(id).collect();
    while let Some(s) = stack.pop() {
        if !seen.insert(s) {
            continue;
        }
        match g.atom(s) {
            Some(a) if a.is_alive() => {
                out.insert(s);
            }
            // Tombstoned (or dangling): conduct order through to its successors.
            _ => stack.extend(g.successors(s)),
        }
    }
    out.into_iter().collect()
}

/// Recursive walk from `from`, appending segments. Detects antichains (>=2 live
/// successors with no order between them) and emits them as prose conflicts.
fn walk(g: &DocGraph, from: AtomId, visited: &mut BTreeSet<AtomId>, out: &mut Vec<Segment>) {
    let mut cursor = from;
    loop {
        let succ = live_successors(g, cursor);
        match succ.as_slice() {
            [] => return,
            [single] => {
                let id = *single;
                if !visited.insert(id) {
                    return;
                }
                if let Some(a) = g.atom(id) {
                    out.push(Segment::Clean(a.content.clone()));
                }
                cursor = id;
            }
            many => {
                // Keep only successors not reachable-from another successor
                // (those would be ordered, not concurrent). Two inserts "after
                // X" with no edge between them are mutually unreachable => a
                // real antichain.
                let antichain: Vec<AtomId> = many
                    .iter()
                    .copied()
                    .filter(|&a| !many.iter().any(|&b| b != a && reachable(g, b, a)))
                    .collect();
                if antichain.len() < 2 {
                    // Successors were actually ordered: follow the minimal one.
                    let next = antichain.first().copied().unwrap_or(many[0]);
                    if !visited.insert(next) {
                        return;
                    }
                    if let Some(at) = g.atom(next) {
                        out.push(Segment::Clean(at.content.clone()));
                    }
                    cursor = next;
                    continue;
                }
                // A genuine prose conflict: each alternative is its own
                // linearization from its head until the branches rejoin (or end).
                let mut alternatives = Vec::new();
                for &head in &antichain {
                    let mut branch = Vec::new();
                    let mut bvisited = visited.clone();
                    let prov = g
                        .atom(head)
                        .map(|a| a.provenance)
                        .unwrap_or(Provenance::GENESIS);
                    if bvisited.insert(head) {
                        if let Some(a) = g.atom(head) {
                            branch.push(Segment::Clean(a.content.clone()));
                        }
                        walk(g, head, &mut bvisited, &mut branch);
                    }
                    coalesce(&mut branch);
                    let text = branch
                        .iter()
                        .map(|s| match s {
                            Segment::Clean(t) => t.clone(),
                            Segment::Conflict(_) => String::new(),
                        })
                        .collect::<String>();
                    alternatives.push(Alternative {
                        head,
                        text,
                        provenance: prov,
                    });
                    visited.insert(head);
                }
                alternatives.sort_by_key(|a| a.head);
                out.push(Segment::Conflict(ConflictRegion {
                    regime: Regime::Prose,
                    field: None,
                    alternatives,
                }));
                return;
            }
        }
    }
}

/// Surface single-valued field clashes (>=2 live assignments) as `Regime::Field`
/// conflict regions, in field-name order.
fn append_field_conflicts(g: &DocGraph, out: &mut Vec<Segment>) {
    let names: Vec<String> = g.field_names().map(|s| s.to_string()).collect();
    for name in names {
        let assigns = g.field(&name);
        if assigns.len() >= 2 {
            let mut alternatives: Vec<Alternative> = assigns
                .iter()
                .map(|a| Alternative {
                    head: AtomId::ROOT,
                    text: a.value.clone(),
                    provenance: a.provenance,
                })
                .collect();
            alternatives.sort_by(|x, y| {
                x.text
                    .cmp(&y.text)
                    .then(x.provenance.patch.cmp(&y.provenance.patch))
            });
            out.push(Segment::Conflict(ConflictRegion {
                regime: Regime::Field,
                field: Some(name),
                alternatives,
            }));
        }
    }
}

/// Is `target` reachable from `start` by following order-edges (through any
/// atoms, alive or dead)? Used to tell "ordered" successors from a true
/// concurrent antichain.
fn reachable(g: &DocGraph, start: AtomId, target: AtomId) -> bool {
    if start == target {
        return true;
    }
    let mut seen = BTreeSet::new();
    let mut stack: Vec<AtomId> = g.successors(start).collect();
    while let Some(s) = stack.pop() {
        if s == target {
            return true;
        }
        if seen.insert(s) {
            stack.extend(g.successors(s));
        }
    }
    false
}

/// Merge adjacent `Clean` segments so the output is canonical (one run per
/// contiguous clean stretch).
fn coalesce(segs: &mut Vec<Segment>) {
    let mut out: Vec<Segment> = Vec::with_capacity(segs.len());
    for seg in segs.drain(..) {
        match (out.last_mut(), &seg) {
            (Some(Segment::Clean(prev)), Segment::Clean(cur)) => prev.push_str(cur),
            _ => out.push(seg),
        }
    }
    *segs = out;
}
