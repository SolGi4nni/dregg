//! # Composition — a document *composed from* cells (the embed algebra)
//!
//! `docs/deos/DOC-CELL-COMPOSITION.md`. Today a dreggverse document IS a cell
//! (1:1): one [`crate::DocGraph`] whose atoms carry `String` content. This module
//! is the bounded prototype of the *next* step: a document **composed from**
//! cells — a section IS a cell, a figure IS a cell — each independently owned,
//! capped, and versioned, laid out into one rendered whole.
//!
//! ## The one new idea: an atom can be a cell-POINTER
//!
//! The composition operator is [`Op::Embed`]: an atom whose content is not a text
//! span but a [`ChildRef`] (a `dregg://` child cell + a [`Pin`]). The parent's
//! layout stays a graph of atoms; an embed-atom is a *hole* the renderer fills by
//! **resolving the child cell through the viewer's membrane**. So a composed
//! document is a *graph of cells*: the parent layout graph plus, by reference,
//! each child's graph.
//!
//! ## Composition is NOT transclusion (the load-bearing distinction)
//!
//! - **Transclusion** (`Dregg2/Deos/Transclusion.lean`) imports a field *VALUE* —
//!   a quote of the bytes a source cell committed at a cited, immutable receipt.
//!   It is a snapshot; it never rots; you cannot edit a quote.
//! - **Composition** (here) embeds a whole *CELL* — a live (or pinned) subtree
//!   with its own atoms, caps, history, and commitment. A [`Pin::Live`] embed
//!   tracks the child's tip; you may edit the child *if you hold its `edit` cap*.
//!
//! ## Why this is additive (does not perturb the existing core)
//!
//! This prototype is **self-contained**: it carries its own small `LayoutGraph`
//! (a parent's layout = embed-atoms + order-edges) rather than widening the
//! existing [`crate::Atom`]. The production shape (DOC-CELL-COMPOSITION.md §2.1)
//! is to make the existing `Atom`'s content a sum `AtomContent::{Text, Embed}`;
//! here we model the embed half in isolation so the prototype is purely additive
//! and the existing patch core is untouched. It REUSES the real
//! [`crate::AtomId`], [`crate::Author`], [`crate::Provenance`], [`crate::Status`],
//! and [`crate::Regime`] so the algebra lines up with the core exactly.
//!
//! ## What it demonstrates
//!
//! - [`Op::Embed`] / [`AtomContent`] / [`ChildRef`] / [`Pin`] / [`EmbedRole`] —
//!   the composition grammar (§2).
//! - [`ChildResolver`] + [`MapResolver`] — the recursive, membrane-gated resolver
//!   seam (the standalone trait; the substrate impl is named wiring, §5.8).
//! - [`content_composed`] — the recursive fold that emits [`Segment::Embedded`]
//!   for embed-atoms, [`Segment::Darkened`] for out-of-cap children, and
//!   [`Segment::Cycle`] for a composition cycle — never forging, never panicking
//!   (§2.3, §7 cycle guard).
//! - [`merge_composed`] — the **product of pushouts** (§4.2): the layout pushout
//!   plus each child's pushout, independently — a child edit can NEVER conflict
//!   with a layout edit (§4.1, the confinement boundary).
//! - [`Op::Embed`]'s [`Pin`] as a single-valued field clash — the one new
//!   cross-boundary conflict ([`Regime::Field`]), pin-divergence (§4.3).

use crate::atom::{AtomId, Author, Provenance, Status};
use crate::regime::Regime;
use std::collections::{BTreeMap, BTreeSet};

// ── §1: the child cell identity (the `dregg://` pointer) ─────────────────────

/// A child cell's identity — content-addressed and unforgeable (the address IS
/// the access grant and the identity). The standalone analogue of the substrate
/// `dregg_types::CellId` / `web_of_cells::DreggUri`.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct CellId(pub u128);

/// Version selection for an embed (§2.1): render the child *live* (its tip), or
/// pin an immutable child receipt (a composition that never rots — the embed
/// analogue of `transclusion_stable_under_source_advance`).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Pin {
    /// Re-resolve to the child's tip every render (the desktop-liveness default).
    Live,
    /// Pin an immutable child receipt — a citation that does not break.
    At(u128),
}

impl Pin {
    /// A canonical string form so a pin can ride the single-valued field-clash
    /// machinery (§4.3): a pin-divergence IS a field clash on this value.
    pub fn key(self) -> String {
        match self {
            Pin::Live => "live".to_string(),
            Pin::At(r) => format!("at:{r:032x}"),
        }
    }
}

/// How an embed lays out. Coarse by design (§7): real layout is a render concern
/// (the servo pass), not an algebra concern. The algebra commits only to *which
/// cell goes where in the order*; *how* it lays out is the renderer's.
///
/// (`Inline` / `Citation` are part of the role vocabulary the layout commits to;
/// not every variant is exercised by the prototype's tests, hence the allow.)
#[allow(dead_code)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum EmbedRole {
    /// A whole section.
    Section,
    /// A figure / illustration.
    Figure,
    /// An inline span.
    Inline,
    /// A block.
    Block,
    /// A live cited cell (a citation that is itself a cell, not a value-quote).
    Citation,
}

/// A `dregg://` name in a NAMESPACE (the standalone analogue of the substrate
/// `web_of_cells::DreggUri` / the nameservice `RESOLVE_TARGET_SLOT` binding). The
/// model: a *namespace cell* holds a map `name -> CellId`; a turn on that cell
/// (a `SetField`) REBINDS a name to a different cell, and any `Name` embed of it
/// FOLLOWS the rebind. It is NOT a cell identity — it is *whatever the namespace
/// currently resolves this name to*. The (`namespace`, `name`) pair is the lookup
/// key; the resolver carries the binding (§2.1b).
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct DreggUri {
    /// The namespace cell that holds the binding (the authority that may rebind).
    pub namespace: CellId,
    /// The name within that namespace (e.g. `"hero-figure"`, `"current-clause"`).
    pub name: String,
}

impl DreggUri {
    /// A `dregg://<namespace>/<name>` reference.
    pub fn new(namespace: CellId, name: impl Into<String>) -> Self {
        DreggUri {
            namespace,
            name: name.into(),
        }
    }
}

/// A reference to a child cell, at a chosen version (§2.1). The TWO ARMS encode
/// the binding-vs-identity distinction (the load-bearing design move):
///
/// - [`ChildRef::Cell`] — **this exact cell** (a raw [`CellId`]). The right handle
///   for IDENTITY: stable, content-addressed; the cell's *state* evolves under it
///   and — for a recoverable identity cell — its AUTHORIZED KEYS rotate IN-STATE
///   (KERI-style: `id = blake3(genesis_pubkey ‖ token_id)`, sealed; rotation is a
///   `SetField` on a key-commitment slot, never the id — see §3.5). So a `Cell`
///   embed is unbroken across the child's recovery: same id, evolved keys.
/// - [`ChildRef::Name`] — **whatever a NAMESPACE currently resolves this name to**
///   (a [`DreggUri`]). A re-bindable reference, not a fixed address: the binding
///   updates with a turn on the namespace cell, and the embed FOLLOWS. The right
///   handle at the application/semantic level ("the cell that plays *this role*
///   right now"), where you do NOT want to be pinned to one identity.
///
/// In BOTH arms the version selection [`Pin`] applies: a `Name` embed can still be
/// pinned to a frozen receipt (the immutable past survives even a rebind, §2.2).
/// This — NOT the child's bytes — is what a parent holds and what the parent's
/// commitment binds (§3.3): for `Cell`, the id+pin; for `Name`, the namespace+name+pin
/// (the indirection itself is committed — a light client follows the same name).
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum ChildRef {
    /// This exact cell (stable identity, evolving state, frozen-or-live).
    Cell(CellId, Pin),
    /// Whatever the namespace currently binds this name to (re-bindable).
    Name(DreggUri, Pin),
}

impl ChildRef {
    /// A live embed of an exact `cell` (the IDENTITY arm, tracking its tip).
    pub fn live(cell: CellId) -> Self {
        ChildRef::Cell(cell, Pin::Live)
    }
    /// An embed of an exact `cell` pinned to receipt `r` (identity, frozen).
    pub fn pinned(cell: CellId, r: u128) -> Self {
        ChildRef::Cell(cell, Pin::At(r))
    }
    /// A live embed of a NAME — re-resolves through the namespace every render, so
    /// it FOLLOWS a rebind (the binding arm, tracking the current binding's tip).
    pub fn live_name(uri: DreggUri) -> Self {
        ChildRef::Name(uri, Pin::Live)
    }
    /// An embed of a NAME pinned to receipt `r` — the name resolves to today's
    /// cell, but the rendered version is frozen at `r` (immutable past, §4).
    pub fn pinned_name(uri: DreggUri, r: u128) -> Self {
        ChildRef::Name(uri, Pin::At(r))
    }

    /// The version selection, regardless of arm.
    pub fn pin(&self) -> Pin {
        match self {
            ChildRef::Cell(_, p) | ChildRef::Name(_, p) => *p,
        }
    }

    /// This ref with its pin replaced (the per-embed [`Op::Repin`] override, §4.3).
    pub fn with_pin(&self, pin: Pin) -> Self {
        match self {
            ChildRef::Cell(c, _) => ChildRef::Cell(*c, pin),
            ChildRef::Name(u, _) => ChildRef::Name(u.clone(), pin),
        }
    }
}

// ── §2: the atom content sum + the embed op ──────────────────────────────────

/// What an atom renders to. The production shape (DOC-CELL-COMPOSITION.md §2.1)
/// makes the existing [`crate::Atom`]'s `content` exactly this sum; the prototype
/// models the [`AtomContent::Embed`] half in isolation.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum AtomContent {
    /// Today's atom — a text span.
    Text(String),
    /// NEW — a cell-pointer the renderer recurses into.
    Embed(ChildRef, EmbedRole),
}

/// A layout atom: an id, content (text OR embed), status, provenance — the same
/// quadruple as the core [`crate::Atom`], with the richer content.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct LayoutAtom {
    /// Stable content-addressed id (a layout vertex; reuses the core [`AtomId`]).
    pub id: AtomId,
    /// Text span or cell-pointer.
    pub content: AtomContent,
    /// Alive or tombstoned (a tombstoned embed = a removed section, monotone).
    pub status: Status,
    /// Who placed this atom / embed.
    pub provenance: Provenance,
}

impl LayoutAtom {
    /// True iff this atom participates in the rendered output.
    pub fn is_alive(&self) -> bool {
        self.status == Status::Alive
    }
}

/// The composition op (§2.1) — the ONE new op beyond `Add`/`Delete`/`Connect`/
/// `SetField`. It introduces a cell-pointer atom ordered after `after`, exactly
/// like `Add` introduces a text atom. (The other ops — tombstone an embed, order
/// embeds, pin an embed — reuse the core grammar; only `Embed` is new.)
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Op {
    /// Place a child cell as an embed-atom, ordered after `after`.
    Embed {
        /// The embed-atom's own layout-vertex id.
        id: AtomId,
        /// Which child, at what version.
        child: ChildRef,
        /// The existing layout atom this embed is ordered after.
        after: AtomId,
        /// How it lays out.
        role: EmbedRole,
    },
    /// Tombstone an embed (remove a section; monotone, no loss).
    Remove {
        /// The embed-atom to tombstone.
        id: AtomId,
    },
    /// Order one embed before another (the layout resolution primitive — collapse
    /// a layout antichain into a chain, exactly like the core `Connect`).
    Order {
        /// The earlier embed.
        from: AtomId,
        /// The later embed.
        to: AtomId,
    },
    /// Set / change an embed's pin (the non-monotone op; two concurrent `Pin`s to
    /// one embed clash — the pin-divergence conflict, §4.3).
    Repin {
        /// The embed whose pin to set.
        id: AtomId,
        /// The pin value.
        pin: Pin,
        /// If true, this supersedes a concurrent clash (a resolution).
        superseding: bool,
    },
}

// ── §2.2: the layout graph (the parent's composition state) ──────────────────

/// The parent document's **layout graph**: a graph of embed-atoms (cell-pointers)
/// with order-edges, plus the per-embed pin store (the non-monotone fragment, so
/// a pin-divergence is a first-class clash). This is the §2.1 `DocGraph`
/// specialized to embed-atoms — the same shape, the same additivity.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct LayoutGraph {
    atoms: BTreeMap<AtomId, LayoutAtom>,
    edges: BTreeMap<AtomId, BTreeSet<AtomId>>,
    /// Per-embed pin assignments: embed-id -> the set of concurrently-assigned
    /// pins (more than one => a pin-divergence clash, §4.3).
    pins: BTreeMap<AtomId, Vec<(Pin, Provenance)>>,
}

impl LayoutGraph {
    /// A fresh, empty layout (just the ROOT sentinel).
    pub fn new() -> Self {
        let mut atoms = BTreeMap::new();
        atoms.insert(
            AtomId::ROOT,
            LayoutAtom {
                id: AtomId::ROOT,
                content: AtomContent::Text(String::new()),
                status: Status::Alive,
                provenance: Provenance::GENESIS,
            },
        );
        LayoutGraph {
            atoms,
            edges: BTreeMap::new(),
            pins: BTreeMap::new(),
        }
    }

    /// Insert (or replace) a layout atom directly — a construction helper for
    /// building a child cell's own layout (a leaf with a marker text atom) outside
    /// the embed grammar (`Op::Embed` only adds embed-atoms; a child's content
    /// atoms are authored in the child's own cell, modeled here directly).
    pub fn insert_atom(&mut self, atom: LayoutAtom) {
        self.atoms.insert(atom.id, atom);
    }

    /// Add an order-edge `from -> to` (the public form of the internal `connect`,
    /// for building a child layout's order outside the patch grammar).
    pub fn connect_pub(&mut self, from: AtomId, to: AtomId) {
        self.connect(from, to);
    }

    /// Look up a layout atom.
    pub fn atom(&self, id: AtomId) -> Option<&LayoutAtom> {
        self.atoms.get(&id)
    }

    /// Iterate every layout atom (alive and dead), in id order — the canonical,
    /// construction-order-independent projection order the substrate commitment
    /// folds over (`crate::substrate::layout_to_heap_map`). A text atom lands in
    /// the atom collection; an embed-atom lands in the `COLL_EMBEDS` collection,
    /// so the parent commitment binds each embed POINTER.
    pub fn atoms(&self) -> impl Iterator<Item = &LayoutAtom> {
        self.atoms.values()
    }

    /// The successors of an atom in the order relation, in id order.
    pub fn successors(&self, id: AtomId) -> impl Iterator<Item = AtomId> + '_ {
        self.edges.get(&id).into_iter().flatten().copied()
    }

    /// The live pins on an embed (>=2 means a pin-divergence clash).
    pub fn pins(&self, id: AtomId) -> &[(Pin, Provenance)] {
        self.pins.get(&id).map(|v| v.as_slice()).unwrap_or(&[])
    }

    /// The effective single pin of an embed: its sole assigned pin, or — if no
    /// `Repin` was applied — the pin baked into its [`Op::Embed`] content. `None`
    /// if there is a clash (>=2 assigned pins).
    pub fn effective_pin(&self, id: AtomId) -> Option<Pin> {
        match self.pins(id) {
            [] => match self.atom(id).map(|a| &a.content) {
                Some(AtomContent::Embed(c, _)) => Some(c.pin()),
                _ => None,
            },
            [(p, _)] => Some(*p),
            _ => None, // a clash: no single effective pin
        }
    }

    /// Apply one op, mutating the layout in place. Forward ops only ever add — so
    /// apply never fails and never destroys (the additivity that keeps merge
    /// total).
    pub fn apply(&mut self, op: &Op, prov: Provenance) {
        match op {
            Op::Embed {
                id,
                child,
                after,
                role,
            } => {
                self.atoms.entry(*id).or_insert(LayoutAtom {
                    id: *id,
                    content: AtomContent::Embed(child.clone(), *role),
                    status: Status::Alive,
                    provenance: prov,
                });
                self.connect(*after, *id);
            }
            Op::Remove { id } => {
                if let Some(a) = self.atoms.get_mut(id) {
                    a.status = Status::Dead;
                }
            }
            Op::Order { from, to } => self.connect(*from, *to),
            Op::Repin {
                id,
                pin,
                superseding,
            } => {
                if *superseding {
                    self.pins.insert(*id, vec![(*pin, prov)]);
                } else {
                    self.assign_pin(*id, *pin, prov);
                }
            }
        }
    }

    /// Apply a whole authored patch (a list of ops with one provenance).
    pub fn apply_patch(&mut self, author: Author, ops: &[Op]) {
        // A content-derived patch id stand-in (so provenance is distinct per
        // author+ops, mirroring the core `Patch::id` shape).
        let prov = Provenance {
            author,
            patch: crate::atom::PatchId(patch_seed(author, ops)),
        };
        for op in ops {
            self.apply(op, prov);
        }
    }

    fn connect(&mut self, from: AtomId, to: AtomId) {
        if from == to {
            return;
        }
        self.edges.entry(from).or_default().insert(to);
    }

    /// Assign a pin additively (keep concurrent assignments so a clash is
    /// representable). Same value dedupes, keeping the lexicographically-first
    /// provenance so merge is order-independent.
    fn assign_pin(&mut self, id: AtomId, pin: Pin, prov: Provenance) {
        let slot = self.pins.entry(id).or_default();
        if let Some(existing) = slot.iter_mut().find(|(p, _)| *p == pin) {
            if (prov.patch, prov.author) < (existing.1.patch, existing.1.author) {
                existing.1 = prov;
            }
            return;
        }
        slot.push((pin, prov));
        slot.sort_by(|a, b| a.0.key().cmp(&b.0.key()).then(a.1.patch.cmp(&b.1.patch)));
    }

    /// Union another layout's atoms, edges, and pins into this one — the engine of
    /// [`merge_layout`] (the layout pushout). Atom statuses join (Dead wins,
    /// monotone); content of a present id is kept (content-addressing); edges
    /// union; pin sets union (so two concurrent pins both survive as a clash).
    pub fn union_in_place(&mut self, other: &LayoutGraph) {
        for (id, a) in &other.atoms {
            self.atoms
                .entry(*id)
                .and_modify(|e| e.status = e.status.join(a.status))
                .or_insert_with(|| a.clone());
        }
        for (from, tos) in &other.edges {
            let slot = self.edges.entry(*from).or_default();
            for to in tos {
                slot.insert(*to);
            }
        }
        for (id, pins) in &other.pins {
            for (p, prov) in pins {
                self.assign_pin(*id, *p, *prov);
            }
        }
    }

    /// The live embed-atoms in document order (the layout linearization). Stops at
    /// a genuine layout antichain (two embeds with no order between them) — that
    /// fork is a layout conflict, surfaced by [`content_composed`].
    fn walk(&self) -> Vec<AtomId> {
        let mut out = Vec::new();
        let mut visited = BTreeSet::new();
        let mut cursor = AtomId::ROOT;
        loop {
            let succ = self.live_successors(cursor);
            let next = match succ.as_slice() {
                [] => return out,
                [single] => *single,
                many => {
                    let antichain: Vec<AtomId> = many
                        .iter()
                        .copied()
                        .filter(|&a| !many.iter().any(|&b| b != a && self.reachable(b, a)))
                        .collect();
                    if antichain.len() >= 2 {
                        return out; // a layout fork: stop at the clean prefix.
                    }
                    antichain.first().copied().unwrap_or(many[0])
                }
            };
            if !visited.insert(next) {
                return out;
            }
            out.push(next);
            cursor = next;
        }
    }

    /// The live successors of `id`, conducting order through tombstoned embeds.
    fn live_successors(&self, id: AtomId) -> Vec<AtomId> {
        let mut seen = BTreeSet::new();
        let mut out = BTreeSet::new();
        let mut stack: Vec<AtomId> = self.successors(id).collect();
        while let Some(s) = stack.pop() {
            if !seen.insert(s) {
                continue;
            }
            match self.atom(s) {
                Some(a) if a.is_alive() => {
                    out.insert(s);
                }
                _ => stack.extend(self.successors(s)),
            }
        }
        out.into_iter().collect()
    }

    fn reachable(&self, start: AtomId, target: AtomId) -> bool {
        if start == target {
            return true;
        }
        let mut seen = BTreeSet::new();
        let mut stack: Vec<AtomId> = self.successors(start).collect();
        while let Some(s) = stack.pop() {
            if s == target {
                return true;
            }
            if seen.insert(s) {
                stack.extend(self.successors(s));
            }
        }
        false
    }

    /// The embed-atoms that currently sit at an unresolved layout antichain (a
    /// layout conflict's heads) — for the conflict view. `None` if the layout is
    /// linear.
    pub fn layout_conflict_heads(&self) -> Option<Vec<AtomId>> {
        // Re-walk; if the walk stopped before exhausting live atoms, the frontier
        // after the last walked atom is the antichain.
        let walked = self.walk();
        let cursor = walked.last().copied().unwrap_or(AtomId::ROOT);
        let succ = self.live_successors(cursor);
        let antichain: Vec<AtomId> = succ
            .iter()
            .copied()
            .filter(|&a| !succ.iter().any(|&b| b != a && self.reachable(b, a)))
            .collect();
        (antichain.len() >= 2).then_some(antichain)
    }
}

/// A small content-derived seed for a patch's provenance (mirrors `Patch::id`'s
/// shape so distinct author+ops get distinct provenance).
fn patch_seed(author: Author, ops: &[Op]) -> u128 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    // Format each op's `Debug` string ONCE (this `Op` doesn't derive `Hash`, and
    // `Debug` is the stable structural projection used here). The old code did the
    // `format!` twice per op (once per hash round) — pure allocation churn for an
    // identical digest; reuse the rendered strings for both rounds instead.
    let rendered: Vec<String> = ops.iter().map(|op| format!("{op:?}")).collect();
    let mut h = DefaultHasher::new();
    0xC0FFEEu64.hash(&mut h);
    author.0.hash(&mut h);
    for s in &rendered {
        s.hash(&mut h);
    }
    let lo = h.finish();
    let mut h2 = DefaultHasher::new();
    for s in &rendered {
        s.hash(&mut h2);
    }
    author.0.hash(&mut h2);
    let hi = h2.finish();
    let v = ((hi as u128) << 64) | (lo as u128);
    if v == 0 { 1 } else { v }
}

// ── §3: the viewer + the membrane-gated resolver seam ────────────────────────

/// A viewer's read authority over child cells (the standalone analogue of the
/// membrane's per-viewer cap set). `caps[&cell]` true => the viewer may read that
/// child; absent/false => the child renders darkened. This is the cap frustum
/// (§3.1) in miniature.
#[derive(Clone, Debug, Default)]
pub struct Viewer {
    /// Which child cells this viewer may read.
    pub may_read: BTreeSet<CellId>,
}

impl Viewer {
    /// A viewer that may read the given cells.
    pub fn able(cells: impl IntoIterator<Item = CellId>) -> Self {
        Viewer {
            may_read: cells.into_iter().collect(),
        }
    }
    /// May this viewer read `cell`?
    pub fn can_read(&self, cell: CellId) -> bool {
        self.may_read.contains(&cell)
    }
}

/// What resolving a child cell yields (§2.3) — NEVER a forge, NEVER a panic.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ChildResolution {
    /// The viewer could read it: the child rendered (recursively — a child may
    /// compose grandchildren).
    Rendered(Box<Rendered>),
    /// The viewer's caps do not reach it: the read was withheld by the membrane,
    /// the citation (which cell) kept. The provenance survives, the bytes do not —
    /// exactly `DreggverseDocument::resolve_for`'s darkened span (§2.3, §3.1).
    Darkened {
        /// Which cell was withheld.
        cell: CellId,
    },
    /// The child cell could not be fetched at all — a real failure, surfaced (the
    /// dangling embed; never swallowed).
    Unresolved {
        /// Which cell failed to resolve.
        cell: CellId,
    },
    /// Resolving this child would close a composition cycle (§7) — surfaced as a
    /// first-class state, never a stack overflow.
    Cycle {
        /// The cell that would re-enter.
        cell: CellId,
    },
    /// A [`ChildRef::Name`] embed whose namespace does not currently bind the name
    /// — an unbound reference (a `Name` is re-bindable, so "not bound right now" is
    /// a first-class state, never a forge; distinct from `Unresolved`, which is a
    /// bound-but-unfetchable cell). The name survives so a later rebind heals it.
    Unbound {
        /// The namespace cell.
        namespace: CellId,
        /// The name that resolves to nothing right now.
        name: String,
    },
}

// ── §2.1b: the namespace resolver (name -> CellId; the re-bindable arm) ───────

/// Resolves a [`DreggUri`] (a name in a namespace) to the [`CellId`] the namespace
/// currently binds it to — the standalone analogue of the substrate nameservice
/// (`cli/src/commands/name.rs`'s `RESOLVE_TARGET_SLOT` `SetField`, or a governed
/// route-table). This is the ONE place a `Name` embed becomes a concrete cell; a
/// REBIND is a turn on the namespace that changes what this returns, and a `Name`
/// embed FOLLOWS it for free (the resolver is re-consulted every render).
pub trait NamespaceResolver {
    /// The cell the namespace currently binds `uri.name` to, or `None` if unbound.
    fn resolve_name(&self, uri: &DreggUri) -> Option<CellId>;
}

/// An in-memory namespace for tests/demos: a map `(namespace, name) -> CellId`.
/// A REBIND is `bind` called again with a different target — exactly the substrate
/// nameservice's single-valued field rewrite, in miniature.
#[derive(Clone, Default, Debug)]
pub struct MapNamespace {
    bindings: BTreeMap<(CellId, String), CellId>,
}

impl MapNamespace {
    /// Bind (or REBIND) `name` in `namespace` to `target` — a turn on the
    /// namespace cell. Returns `self` for builder use; the last bind wins (a
    /// single-valued field, like the substrate's `SetField`).
    pub fn bind(mut self, namespace: CellId, name: impl Into<String>, target: CellId) -> Self {
        self.bindings.insert((namespace, name.into()), target);
        self
    }

    /// Rebind in place (the mutating form of a namespace turn).
    pub fn rebind(&mut self, namespace: CellId, name: impl Into<String>, target: CellId) {
        self.bindings.insert((namespace, name.into()), target);
    }
}

impl NamespaceResolver for MapNamespace {
    fn resolve_name(&self, uri: &DreggUri) -> Option<CellId> {
        self.bindings
            .get(&(uri.namespace, uri.name.clone()))
            .copied()
    }
}

/// A namespace that binds nothing — every `Name` resolves to [`ChildResolution::Unbound`].
/// (The default for a `Cell`-only resolver: identity embeds never consult it.)
#[derive(Clone, Copy, Default, Debug)]
pub struct NoNamespace;

impl NamespaceResolver for NoNamespace {
    fn resolve_name(&self, _uri: &DreggUri) -> Option<CellId> {
        None
    }
}

/// The recursive resolver seam (§5.3): how an embed-atom resolves its child cell
/// for a viewer. The standalone crate ships this trait + [`MapResolver`]; the
/// `substrate` feature plugs in the real `dregg://` fetch + `Membrane::project`
/// (the named §5.8 wiring). It is handed the viewer's caps and can ONLY return an
/// attenuated view — the non-amplification (`transclusion_no_amplify`) is
/// structural here (§3.2).
pub trait ChildResolver {
    /// Resolve a [`ChildRef`] that has ALREADY been reduced to a concrete `cell`
    /// (the [`ChildRef::Name`] arm's namespace step is done by [`Self::resolve`]).
    /// An implementation MUST NOT return `Rendered` for a viewer that `!can_read`
    /// the cell (that would be an amplification) — it returns
    /// [`ChildResolution::Darkened`] instead.
    fn resolve_cell(
        &self,
        cell: CellId,
        viewer: &Viewer,
        in_progress: &BTreeSet<CellId>,
    ) -> ChildResolution;

    /// The namespace this resolver consults for the [`ChildRef::Name`] arm. The
    /// default is [`NoNamespace`] (a `Cell`-only resolver: every `Name` is
    /// `Unbound`). A resolver with a namespace overrides this — the ONE step that
    /// turns a re-bindable name into a concrete identity, re-run every render so a
    /// `Name` embed FOLLOWS a rebind.
    fn namespace(&self) -> &dyn NamespaceResolver {
        &NoNamespace
    }

    /// The concrete cell a ref points to RIGHT NOW (the identity for a `Cell` arm;
    /// the namespace's current binding for a `Name` arm; `None` iff a `Name` is
    /// unbound). This is the observable a rebind moves — independent of viewer/caps.
    fn resolved_cell(&self, child: &ChildRef) -> Option<CellId> {
        match child {
            ChildRef::Cell(cell, _) => Some(*cell),
            ChildRef::Name(uri, _) => self.namespace().resolve_name(uri),
        }
    }

    /// Resolve `child` for `viewer` (§2.3) — the public seam. For a
    /// [`ChildRef::Name`], FIRST resolve the name through the namespace (`Unbound`
    /// if it binds nothing right now), THEN resolve the resulting cell exactly as a
    /// [`ChildRef::Cell`] would. This is the binding-vs-identity split made
    /// operational: identity goes straight to the cell; a name detours through the
    /// (re-bindable) namespace, so the SAME embed renders a different cell after a
    /// rebind, without the embed itself changing.
    fn resolve(
        &self,
        child: &ChildRef,
        viewer: &Viewer,
        in_progress: &BTreeSet<CellId>,
    ) -> ChildResolution {
        match child {
            // Identity arm: this exact cell, directly.
            ChildRef::Cell(cell, _) => self.resolve_cell(*cell, viewer, in_progress),
            // Binding arm: name -> CellId via the namespace, THEN resolve the cell.
            ChildRef::Name(uri, _) => match self.namespace().resolve_name(uri) {
                Some(cell) => self.resolve_cell(cell, viewer, in_progress),
                None => ChildResolution::Unbound {
                    namespace: uri.namespace,
                    name: uri.name.clone(),
                },
            },
        }
    }
}

/// An in-memory resolver for tests/demos: a map from `CellId` to that child's own
/// [`LayoutGraph`], plus a [`MapNamespace`] for the [`ChildRef::Name`] arm. It
/// enforces the membrane gate (out-of-cap => darkened), the cycle guard, the name
/// step, and the recursion (a resolved child is itself folded). The substrate
/// resolver is the same shape over `WebOfCells` (cells + the nameservice binding)
/// + `Membrane`.
#[derive(Clone, Default)]
pub struct MapResolver {
    /// Each child cell's layout (so a child may itself compose grandchildren).
    pub cells: BTreeMap<CellId, LayoutGraph>,
    /// The namespace consulted for `Name` embeds (the re-bindable arm).
    pub names: MapNamespace,
}

impl MapResolver {
    /// Register a child cell's layout.
    pub fn with(mut self, cell: CellId, layout: LayoutGraph) -> Self {
        self.cells.insert(cell, layout);
        self
    }

    /// Install a namespace binding `name -> target` (a turn on the namespace cell).
    pub fn with_name(mut self, namespace: CellId, name: impl Into<String>, target: CellId) -> Self {
        self.names = std::mem::take(&mut self.names).bind(namespace, name, target);
        self
    }

    /// REBIND a name to a different target (a later namespace turn) — a `Name` embed
    /// that resolved to the old target now resolves to the new one.
    pub fn rebind(&mut self, namespace: CellId, name: impl Into<String>, target: CellId) {
        self.names.rebind(namespace, name, target);
    }
}

impl ChildResolver for MapResolver {
    fn namespace(&self) -> &dyn NamespaceResolver {
        &self.names
    }

    fn resolve_cell(
        &self,
        cell: CellId,
        viewer: &Viewer,
        in_progress: &BTreeSet<CellId>,
    ) -> ChildResolution {
        // (1) cycle guard (§7): never re-enter a cell already being rendered.
        if in_progress.contains(&cell) {
            return ChildResolution::Cycle { cell };
        }
        // (2) the membrane gate (§3.1/§3.2): out-of-cap => darkened, NOT amplified.
        if !viewer.can_read(cell) {
            return ChildResolution::Darkened { cell };
        }
        // (3) the fetch: a registered cell resolves; an unknown one is a real
        //     dangling failure.
        match self.cells.get(&cell) {
            Some(layout) => {
                // The recursion: render the child, marking it in-progress so a
                // grandchild that points back here trips the cycle guard.
                let mut nested = in_progress.clone();
                nested.insert(cell);
                let rendered = fold(layout, viewer, self, &nested);
                ChildResolution::Rendered(Box::new(rendered))
            }
            None => ChildResolution::Unresolved { cell },
        }
    }
}

// ── §2.3: the recursive, membrane-gated fold (the render) ────────────────────

/// One unit of composed rendered output. A composed document is a sequence of
/// these — clean prefix, embedded children (resolved per-viewer), a layout
/// conflict where two embeds are unordered.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Segment {
    /// A clean run of the parent's own TEXT content (a layout-atom whose content
    /// is [`AtomContent::Text`]). The composed fold interleaves these with the
    /// embedded children — closing the "named interleave point" the prototype
    /// used to skip (DREGG-DOCUMENT-DESIGN §2: text is the core's job, but the
    /// composed render must still emit it in order, not drop it).
    Text(String),
    /// An embedded child cell, resolved through the viewer's membrane. Carries the
    /// role, who placed it (a fact), the child ref, and the resolution.
    Embedded {
        /// How it lays out.
        role: EmbedRole,
        /// Who placed this embed.
        placed_by: Author,
        /// Which child + version (the REF — a `Cell` id or a `Name` in a namespace).
        child: ChildRef,
        /// The concrete cell the ref resolved to THIS render: for a `Cell` ref it is
        /// the ref's id; for a `Name` ref it is whatever the namespace currently
        /// binds — so a rebind changes this even though `child` is unchanged. `None`
        /// iff a `Name` is currently unbound.
        resolved_cell: Option<CellId>,
        /// The per-viewer resolution (Rendered / Darkened / Unresolved / Cycle / Unbound).
        resolution: ChildResolution,
    },
    /// A layout conflict: >=2 embeds at one position with no order between them. A
    /// first-class state (the §4.1 layout antichain), each alternative tagged with
    /// who placed it. Resolved by an [`Op::Order`].
    LayoutConflict {
        /// The clashing embed atoms (head id + who placed it + the child ref).
        alternatives: Vec<(AtomId, Author, ChildRef)>,
    },
    /// A pin-divergence conflict (§4.3): two authors pinned the SAME embed to
    /// DIFFERENT receipts. The one new cross-boundary clash — a [`Regime::Field`]
    /// non-monotone conflict on the embed's pin, resolved by choosing a pin.
    PinConflict {
        /// The embed whose pin is contested.
        embed: AtomId,
        /// The clashing pins, each with who chose it.
        alternatives: Vec<(Pin, Author)>,
    },
}

impl Segment {
    /// The regime a conflict segment belongs to (the §4 classifier reading): a
    /// layout antichain is illusory/`Prose` (unilaterally orderable); a pin
    /// divergence is a real `Field` clash (may need consensus). `None` for an
    /// embedded (non-conflict) segment.
    pub fn regime(&self) -> Option<Regime> {
        match self {
            Segment::Text(_) | Segment::Embedded { .. } => None,
            Segment::LayoutConflict { .. } => Some(Regime::Prose),
            Segment::PinConflict { .. } => Some(Regime::Field),
        }
    }
}

/// The full composed render: a sequence of segments in document order.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct Rendered {
    /// The segments in order.
    pub segments: Vec<Segment>,
}

impl Rendered {
    /// True iff the composed document carries an unresolved layout or pin conflict.
    pub fn has_conflict(&self) -> bool {
        self.segments.iter().any(|s| s.regime().is_some())
    }
    /// True iff any embedded child rendered darkened (out-of-cap for this viewer).
    pub fn has_darkened(&self) -> bool {
        self.segments.iter().any(|s| {
            matches!(
                s,
                Segment::Embedded {
                    resolution: ChildResolution::Darkened { .. },
                    ..
                }
            )
        })
    }
    /// The cells embedded at the top level (in order) — the RESOLVED cell each
    /// embed ref pointed to this render (a `Name` reports its current binding's
    /// cell; an unbound `Name` is skipped). This is the observable a rebind moves.
    pub fn embedded_cells(&self) -> Vec<CellId> {
        self.segments
            .iter()
            .filter_map(|s| match s {
                Segment::Embedded { resolved_cell, .. } => *resolved_cell,
                _ => None,
            })
            .collect()
    }
}

/// Render a composed document for a viewer (§2.3) — the public entry. Walks the
/// parent layout, resolving each embed-atom's child cell through `resolver`
/// (membrane-gated), recursing into readable children, and surfacing layout/pin
/// conflicts as first-class states.
pub fn content_composed(
    parent: &LayoutGraph,
    viewer: &Viewer,
    resolver: &impl ChildResolver,
) -> Rendered {
    fold(parent, viewer, resolver, &BTreeSet::new())
}

/// The recursive worker. `in_progress` is the chain of cells being rendered above
/// this one (the cycle guard).
fn fold(
    parent: &LayoutGraph,
    viewer: &Viewer,
    resolver: &impl ChildResolver,
    in_progress: &BTreeSet<CellId>,
) -> Rendered {
    let mut out = Rendered::default();

    // The layout linearization — computed ONCE and reused for both the embed
    // render below and the pin-divergence pass (it was re-walked per use).
    let walked = parent.walk();

    for &id in &walked {
        let atom = match parent.atom(id) {
            Some(a) => a,
            None => continue,
        };
        match &atom.content {
            AtomContent::Text(t) => {
                // The interleave point, now CLOSED: a text layout-atom emits its
                // run in document order alongside the embeds (previously skipped).
                // Empty text (e.g. the ROOT sentinel or a leaf marker with no run)
                // contributes nothing, so the pure-embed layouts still render as
                // before — this only ADDS the missing text, it never reorders.
                if !t.is_empty() {
                    out.segments.push(Segment::Text(t.clone()));
                }
            }
            AtomContent::Embed(child, role) => {
                // The effective pin (a `Repin` override, else the ref's own pin)
                // rides the ref regardless of arm — a `Name` embed is pinnable too.
                let child_now = child.with_pin(parent.effective_pin(id).unwrap_or(child.pin()));
                // The name step (the re-bindable arm): resolve the ref to a concrete
                // cell THIS render, so a rebind on the namespace moves the embed.
                let resolved_cell = resolver.resolved_cell(&child_now);
                // Resolve through the membrane — out-of-cap darkens, a cycle trips
                // the guard, an unknown cell is unresolved, an unbound name is
                // unbound, a readable cell recurses.
                let resolution = resolver.resolve(&child_now, viewer, in_progress);
                out.segments.push(Segment::Embedded {
                    role: *role,
                    placed_by: atom.provenance.author,
                    child: child_now,
                    resolved_cell,
                    resolution,
                });
            }
        }
    }

    // Surface a layout conflict (two embeds unordered at the frontier).
    if let Some(heads) = parent.layout_conflict_heads() {
        let alternatives = heads
            .iter()
            .filter_map(|&h| {
                parent.atom(h).and_then(|a| match &a.content {
                    AtomContent::Embed(c, _) => Some((h, a.provenance.author, c.clone())),
                    _ => None,
                })
            })
            .collect();
        out.segments.push(Segment::LayoutConflict { alternatives });
    }

    // Surface pin-divergence conflicts (§4.3) — an embed with >=2 live pins.
    for &id in &walked {
        let pins = parent.pins(id);
        if pins.len() >= 2 {
            let mut alternatives: Vec<(Pin, Author)> =
                pins.iter().map(|(p, prov)| (*p, prov.author)).collect();
            alternatives.sort_by(|a, b| a.0.key().cmp(&b.0.key()));
            out.segments.push(Segment::PinConflict {
                embed: id,
                alternatives,
            });
        }
    }

    out
}

// ── §4: the product-of-pushouts merge ────────────────────────────────────────

/// The layout pushout — the total union merge of two parent layouts (§4.1). Same
/// algebra as the core [`crate::merge`], on embed-atoms: total, commutative,
/// associative, idempotent.
pub fn merge_layout(a: &LayoutGraph, b: &LayoutGraph) -> LayoutGraph {
    let mut out = a.clone();
    out.union_in_place(b);
    out
}

/// A composed document = a parent layout + the (in-memory) children it embeds.
/// This is the prototype's standalone bundling; on the substrate the children are
/// resolved live through `dregg://`, never bundled.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct Composed {
    /// The parent's layout graph.
    pub layout: LayoutGraph,
    /// Each embedded child's own layout (so merge can push out children too).
    pub children: BTreeMap<CellId, LayoutGraph>,
}

/// The composed merge (§4.2) — the **product of pushouts**: the layout pushout
/// PLUS each child's pushout, independently. A child-content edit and a
/// parent-layout edit can NEVER conflict (disjoint graphs — the §4.1 confinement
/// boundary). Commutativity/associativity/idempotence hold componentwise.
pub fn merge_composed(a: &Composed, b: &Composed) -> Composed {
    let layout = merge_layout(&a.layout, &b.layout);
    let mut children: BTreeMap<CellId, LayoutGraph> = a.children.clone();
    for (cell, cb) in &b.children {
        children
            .entry(*cell)
            .and_modify(|ca| ca.union_in_place(cb)) // each child's own pushout
            .or_insert_with(|| cb.clone());
    }
    Composed { layout, children }
}

// ── §6: THE DESKTOP AS A COMPOSED DOCUMENT (the reflexive weld) ───────────────
//
// `docs/deos/DOC-CELL-COMPOSITION.md §6`: "the whole starbridge is kinda like a
// cell document." The flat projection (`crate::desktop`, substrate-gated) reads a
// workspace as TEXT atoms (`owner ‖ root ‖ digest`) chained in z-order. THIS reads
// it through the COMPOSITION algebra: each surface is an [`Op::Embed`] of the
// surface's OWNER CELL, so the workspace is a *graph of cells* — the root layout
// plus, by reference, each window's cell. That is the sharper convergence: not a
// flat list, but the SAME `Op::Embed` tree the document language is, so the desktop
// inherits — through the SAME fold ([`content_composed`]) — the per-viewer membrane
// (an out-of-cap window DARKENS, never forges), forkability/time-travel (the layout
// graph is a `merge`-able pushout), and the cycle guard (a window that mirrors the
// whole desktop trips it, never a stack overflow).
//
// This module is standalone (no substrate): a [`DesktopSurface`] is the
// renderer-agnostic shape the cockpit's `compositor::CompositedSurface` maps onto
// (the cockpit adapter does the substrate-side `CellId`→`u128` reduction). The
// projection [`scene_to_composed`] is built by APPLYING ordinary [`Op::Embed`] /
// [`Op::Order`] ops — a desktop layout authored by exactly the embed grammar a
// composed prose document uses.

/// A renderer-agnostic description of one cockpit surface for the COMPOSED reading:
/// the owning cell, the z-layer (paint order), and whether it holds focus. The
/// `owner` is the child cell the surface embeds — the window IS an embed of that
/// cell, resolved per-viewer through the membrane.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct DesktopSurface {
    /// The owning cell — the child this window embeds.
    pub owner: CellId,
    /// The z-layer (paint order, back-to-front). Defines the embed order.
    pub z_layer: i64,
    /// Whether this surface holds input focus.
    pub focus_flag: bool,
}

impl DesktopSurface {
    /// A surface owned by `owner` at paint layer `z` (unfocused).
    pub fn new(owner: CellId, z: i64) -> Self {
        DesktopSurface {
            owner,
            z_layer: z,
            focus_flag: false,
        }
    }
    /// This surface holding focus.
    pub fn focused(mut self) -> Self {
        self.focus_flag = true;
        self
    }
}

/// The seed domain for desktop embed-atom ids (so a window embed never collides
/// with a prose embed of the same cell).
const DESKTOP_EMBED_SEED: u64 = 0xDE5C_0DE5;

/// The content-addressed embed-atom id a surface projects to (so a later
/// reorder/remove targets the SAME embed-atom [`scene_to_composed`] created).
pub fn surface_embed_id(s: &DesktopSurface) -> AtomId {
    AtomId::derive(DESKTOP_EMBED_SEED, &format!("window:{}", s.owner.0))
}

/// Project a workspace (paint-order `surfaces`) into a COMPOSED document
/// ([`LayoutGraph`]) — THE WELD. Each surface becomes an [`Op::Embed`] of its owner
/// cell, chained after the previous so the layout walk IS the paint order. A
/// focused surface is embedded with [`EmbedRole::Block`] (the focus holder is the
/// active block); the rest are [`EmbedRole::Section`]. The `author` binds into each
/// embed-atom's provenance. The window is a LIVE embed ([`Pin::Live`]) — it tracks
/// the owner cell's tip, the desktop-liveness default.
pub fn scene_to_composed(surfaces: &[DesktopSurface], author: Author) -> LayoutGraph {
    let mut layout = LayoutGraph::new();
    let mut prev = AtomId::ROOT;
    let mut ops: Vec<Op> = Vec::with_capacity(surfaces.len());
    for s in surfaces {
        let id = surface_embed_id(s);
        let role = if s.focus_flag {
            EmbedRole::Block
        } else {
            EmbedRole::Section
        };
        ops.push(Op::Embed {
            id,
            child: ChildRef::live(s.owner),
            after: prev,
            role,
        });
        prev = id;
    }
    layout.apply_patch(author, &ops);
    layout
}

/// A resolver over a live workspace: each surface's owner cell resolves to a leaf
/// cell layout (the window's content). The standalone analogue of the cockpit's
/// per-window surface fetch; the substrate adapter plugs the real `dregg://` read +
/// `Membrane::project` in its place (`starbridge-v2/src/cell_transclusion.rs`).
pub fn workspace_resolver(surfaces: &[DesktopSurface]) -> MapResolver {
    let mut r = MapResolver::default();
    for s in surfaces {
        // Each window's content is the owner cell's own (leaf) layout. A leaf
        // carries a single marker text atom so the fold renders it; a real window
        // resolves its full cell layout (and may itself compose grandchildren).
        let mut g = LayoutGraph::new();
        let marker = AtomId::derive(0x5_DE5C, &format!("content:{}", s.owner.0));
        g.insert_atom(LayoutAtom {
            id: marker,
            content: AtomContent::Text(format!("window {:x}", s.owner.0)),
            status: Status::Alive,
            provenance: Provenance::GENESIS,
        });
        g.connect_pub(AtomId::ROOT, marker);
        r = r.with(s.owner, g);
    }
    r
}

/// Tombstone (close/minimize) one surface in the composed reading: an [`Op::Remove`]
/// on the surface's embed-atom (monotone — the embed stays in the graph,
/// time-travellable, off the rendered walk). The reflexive edit: closing a window
/// is the embed grammar editing the document that IS the desktop.
pub fn close_surface(s: &DesktopSurface) -> Op {
    Op::Remove {
        id: surface_embed_id(s),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn root() -> AtomId {
        AtomId::ROOT
    }

    /// Mint a layout-atom id for an embed (content-addressed over the cell + a seed).
    fn embed_id(seed: u64, cell: CellId) -> AtomId {
        AtomId::derive(seed, &format!("embed:{}", cell.0))
    }

    fn leaf_cell(text: &str) -> LayoutGraph {
        // A "leaf" child: a layout with a single text atom (stands in for a child
        // whose content the resolver would render; for the prototype its presence
        // is what matters — the recursion folds it).
        let mut g = LayoutGraph::new();
        let id = AtomId::derive(99, text);
        g.atoms.insert(
            id,
            LayoutAtom {
                id,
                content: AtomContent::Text(text.to_string()),
                status: Status::Alive,
                provenance: Provenance {
                    author: Author(99),
                    patch: crate::atom::PatchId(1),
                },
            },
        );
        g.connect(AtomId::ROOT, id);
        g
    }

    // ── §2: the embed operator places a cell-pointer ─────────────────────────

    #[test]
    fn embed_places_a_cell_pointer() {
        let fig = CellId(0xF1);
        let eid = embed_id(1, fig);
        let mut layout = LayoutGraph::new();
        layout.apply_patch(
            Author(1),
            &[Op::Embed {
                id: eid,
                child: ChildRef::live(fig),
                after: root(),
                role: EmbedRole::Figure,
            }],
        );
        let viewer = Viewer::able([fig]);
        let resolver = MapResolver::default().with(fig, leaf_cell("a figure"));
        let r = content_composed(&layout, &viewer, &resolver);
        assert_eq!(r.embedded_cells(), vec![fig], "the figure cell is embedded");
        assert!(!r.has_conflict());
    }

    // ── §3.1/§3.2: ownership — an out-of-cap child DARKENS, never amplifies ───

    #[test]
    fn out_of_cap_child_darkens_not_amplifies() {
        let secret = CellId(0x5EC);
        let eid = embed_id(1, secret);
        let mut layout = LayoutGraph::new();
        layout.apply_patch(
            Author(1),
            &[Op::Embed {
                id: eid,
                child: ChildRef::live(secret),
                after: root(),
                role: EmbedRole::Section,
            }],
        );
        // The resolver KNOWS the cell, but the viewer lacks the cap.
        let resolver = MapResolver::default().with(secret, leaf_cell("classified"));
        let blind = Viewer::default(); // no caps
        let r = content_composed(&layout, &blind, &resolver);
        assert!(r.has_darkened(), "an out-of-cap child renders darkened");
        // The citation (which cell) survives; the bytes do not.
        assert_eq!(r.embedded_cells(), vec![secret], "the citation is kept");
        match &r.segments[0] {
            Segment::Embedded {
                resolution: ChildResolution::Darkened { cell },
                ..
            } => {
                assert_eq!(*cell, secret)
            }
            other => panic!("expected darkened, got {other:?}"),
        }

        // A viewer WITH the cap sees it rendered — the membrane is the only gate.
        let cleared = Viewer::able([secret]);
        let r2 = content_composed(&layout, &cleared, &resolver);
        assert!(!r2.has_darkened(), "a cleared viewer reads the child");
    }

    #[test]
    fn unknown_child_is_unresolved_not_panic() {
        let gone = CellId(0xDEAD);
        let eid = embed_id(1, gone);
        let mut layout = LayoutGraph::new();
        layout.apply_patch(
            Author(1),
            &[Op::Embed {
                id: eid,
                child: ChildRef::live(gone),
                after: root(),
                role: EmbedRole::Block,
            }],
        );
        let resolver = MapResolver::default(); // empty — the cell does not resolve
        let viewer = Viewer::able([gone]);
        let r = content_composed(&layout, &viewer, &resolver);
        match &r.segments[0] {
            Segment::Embedded {
                resolution: ChildResolution::Unresolved { cell },
                ..
            } => {
                assert_eq!(*cell, gone, "a dangling embed is surfaced, not swallowed")
            }
            other => panic!("expected unresolved, got {other:?}"),
        }
    }

    // ── §7: the cycle guard ──────────────────────────────────────────────────

    #[test]
    fn composition_cycle_is_a_state_not_a_stack_overflow() {
        let a = CellId(0xAA);
        let b = CellId(0xBB);
        // A embeds B; B embeds A — a cycle.
        let mut la = LayoutGraph::new();
        la.apply_patch(
            Author(1),
            &[Op::Embed {
                id: embed_id(1, b),
                child: ChildRef::live(b),
                after: root(),
                role: EmbedRole::Section,
            }],
        );
        let mut lb = LayoutGraph::new();
        lb.apply_patch(
            Author(1),
            &[Op::Embed {
                id: embed_id(1, a),
                child: ChildRef::live(a),
                after: root(),
                role: EmbedRole::Section,
            }],
        );
        let resolver = MapResolver::default()
            .with(a, la.clone())
            .with(b, lb.clone());
        let viewer = Viewer::able([a, b]);
        // Render A: A -> B -> (A again, cycle).
        let r = content_composed(&la, &viewer, &resolver);
        // Top level is the embed of B (rendered); inside it, the embed of A cycles.
        let found_cycle = format!("{r:?}").contains("Cycle");
        assert!(
            found_cycle,
            "the A->B->A cycle is surfaced as a Cycle state"
        );
    }

    // ── §4.1: a layout edit and a child edit NEVER conflict ──────────────────

    #[test]
    fn layout_edit_and_child_edit_do_not_conflict() {
        let fig = CellId(0xF1);
        let eid = embed_id(1, fig);

        // Base: one embed of the figure.
        let mut base_layout = LayoutGraph::new();
        base_layout.apply_patch(
            Author(1),
            &[Op::Embed {
                id: eid,
                child: ChildRef::live(fig),
                after: root(),
                role: EmbedRole::Figure,
            }],
        );
        let base_child = leaf_cell("figure v1");
        let base = Composed {
            layout: base_layout,
            children: BTreeMap::from([(fig, base_child)]),
        };

        // Author A reorders/adds a second embed in the LAYOUT.
        let other = CellId(0xF2);
        let mut a = base.clone();
        a.layout.apply_patch(
            Author(1),
            &[Op::Embed {
                id: embed_id(2, other),
                child: ChildRef::live(other),
                after: eid,
                role: EmbedRole::Figure,
            }],
        );
        a.children.insert(other, leaf_cell("second figure"));

        // Author B edits the embedded CHILD (the figure cell itself).
        let mut b = base.clone();
        let extra = AtomId::derive(7, "figure caption");
        let child = b.children.get_mut(&fig).unwrap();
        child.atoms.insert(
            extra,
            LayoutAtom {
                id: extra,
                content: AtomContent::Text("figure caption".into()),
                status: Status::Alive,
                provenance: Provenance {
                    author: Author(2),
                    patch: crate::atom::PatchId(5),
                },
            },
        );
        child.connect(AtomId::ROOT, extra);

        // The composed merge: layout pushout + child pushout, independently.
        let merged = merge_composed(&a, &b);

        // BOTH edits survived, and there is NO cross-conflict: the layout has two
        // embeds, the child has its new caption — disjoint graphs, clean union.
        let viewer = Viewer::able([fig, other]);
        let resolver = MapResolver {
            names: Default::default(),
            cells: merged.children.clone(),
        };
        let r = content_composed(&merged.layout, &viewer, &resolver);
        assert_eq!(
            r.embedded_cells(),
            vec![fig, other],
            "the layout edit (second embed) survived"
        );
        assert!(
            !r.has_conflict(),
            "a layout edit and a child edit never cross-conflict (disjoint cells)"
        );
        // And the child's own edit is in the merged child graph.
        assert!(
            merged.children[&fig].atom(extra).is_some(),
            "the child-content edit survived in the child's own graph"
        );
    }

    // ── §4.2: the layout pushout is commutative + idempotent ─────────────────

    #[test]
    fn layout_merge_is_commutative_and_idempotent() {
        let f1 = CellId(0xF1);
        let f2 = CellId(0xF2);
        let mut base = LayoutGraph::new();
        base.apply_patch(
            Author(1),
            &[Op::Embed {
                id: embed_id(1, f1),
                child: ChildRef::live(f1),
                after: root(),
                role: EmbedRole::Figure,
            }],
        );
        let head = embed_id(1, f1);

        let mut a = base.clone();
        a.apply_patch(
            Author(1),
            &[Op::Embed {
                id: embed_id(2, f2),
                child: ChildRef::live(f2),
                after: head,
                role: EmbedRole::Figure,
            }],
        );
        let mut b = base.clone();
        b.apply_patch(
            Author(2),
            &[Op::Remove { id: head }], // B removes the first embed
        );

        assert_eq!(merge_layout(&a, &b), merge_layout(&b, &a), "commutative");
        let m = merge_layout(&a, &b);
        assert_eq!(merge_layout(&m, &m), m, "idempotent");
        assert_eq!(
            merge_layout(&m, &base),
            m,
            "absorbs the base (idempotent over prefix)"
        );
    }

    // ── §4.3: the one new cross-boundary conflict — pin divergence ───────────

    #[test]
    fn concurrent_pins_clash_as_a_field_conflict() {
        let fig = CellId(0xF1);
        let eid = embed_id(1, fig);
        let mut base = LayoutGraph::new();
        base.apply_patch(
            Author(1),
            &[Op::Embed {
                id: eid,
                child: ChildRef::live(fig),
                after: root(),
                role: EmbedRole::Figure,
            }],
        );

        // Author A pins the figure at v3; Author B at v5 — concurrently.
        let mut a = base.clone();
        a.apply_patch(
            Author(1),
            &[Op::Repin {
                id: eid,
                pin: Pin::At(3),
                superseding: false,
            }],
        );
        let mut b = base.clone();
        b.apply_patch(
            Author(2),
            &[Op::Repin {
                id: eid,
                pin: Pin::At(5),
                superseding: false,
            }],
        );

        let merged = merge_layout(&a, &b);
        assert_eq!(merged.pins(eid).len(), 2, "both pins survive as a clash");
        assert_eq!(
            merged.effective_pin(eid),
            None,
            "no single effective pin (clash)"
        );

        let viewer = Viewer::able([fig]);
        let resolver = MapResolver::default().with(fig, leaf_cell("figure"));
        let r = content_composed(&merged, &viewer, &resolver);
        let pin_conflict = r.segments.iter().find_map(|s| match s {
            Segment::PinConflict { alternatives, .. } => Some(alternatives.clone()),
            _ => None,
        });
        let alts = pin_conflict.expect("a pin-divergence conflict is surfaced");
        assert_eq!(alts.len(), 2, "two pins clash");
        // It is a FIELD-regime (non-monotone, may-need-consensus) conflict.
        let seg = r
            .segments
            .iter()
            .find(|s| matches!(s, Segment::PinConflict { .. }))
            .unwrap();
        assert_eq!(
            seg.regime(),
            Some(Regime::Field),
            "pin divergence is a Field clash"
        );
        assert!(Regime::Field.needs_consensus());

        // A superseding repin (a resolution) collapses the clash.
        let mut resolved = merged.clone();
        resolved.apply_patch(
            Author(1),
            &[Op::Repin {
                id: eid,
                pin: Pin::At(5),
                superseding: true,
            }],
        );
        assert_eq!(
            resolved.effective_pin(eid),
            Some(Pin::At(5)),
            "resolved to one pin"
        );
        let r2 = content_composed(&resolved, &viewer, &resolver);
        assert!(!r2.has_conflict(), "the resolution clears the pin conflict");
    }

    // ── §4.1: a genuine LAYOUT conflict (two embeds, no order) is first-class ─

    #[test]
    fn concurrent_embeds_at_one_position_are_a_layout_conflict() {
        let f1 = CellId(0xF1);
        let f2 = CellId(0xF2);
        let base = LayoutGraph::new();

        // Two authors each place a DIFFERENT figure right after ROOT, concurrently
        // — no order between them => a layout antichain.
        let mut a = base.clone();
        a.apply_patch(
            Author(1),
            &[Op::Embed {
                id: embed_id(1, f1),
                child: ChildRef::live(f1),
                after: root(),
                role: EmbedRole::Figure,
            }],
        );
        let mut b = base.clone();
        b.apply_patch(
            Author(2),
            &[Op::Embed {
                id: embed_id(2, f2),
                child: ChildRef::live(f2),
                after: root(),
                role: EmbedRole::Figure,
            }],
        );
        let merged = merge_layout(&a, &b);

        let viewer = Viewer::able([f1, f2]);
        let resolver = MapResolver::default()
            .with(f1, leaf_cell("fig 1"))
            .with(f2, leaf_cell("fig 2"));
        let r = content_composed(&merged, &viewer, &resolver);
        let layout_conflict = r.segments.iter().find_map(|s| match s {
            Segment::LayoutConflict { alternatives } => Some(alternatives.clone()),
            _ => None,
        });
        let alts = layout_conflict.expect("a layout conflict is surfaced");
        assert_eq!(alts.len(), 2, "two embeds clash at one position");
        // It is a PROSE-regime (illusory, unilaterally orderable) conflict.
        let seg = r
            .segments
            .iter()
            .find(|s| matches!(s, Segment::LayoutConflict { .. }))
            .unwrap();
        assert_eq!(seg.regime(), Some(Regime::Prose));
        assert!(
            !Regime::Prose.needs_consensus(),
            "a layout order is unilaterally resolvable"
        );

        // Resolve by ordering f1 before f2 (the layout resolution primitive).
        let mut resolved = merged.clone();
        resolved.apply_patch(
            Author(1),
            &[Op::Order {
                from: embed_id(1, f1),
                to: embed_id(2, f2),
            }],
        );
        let r2 = content_composed(&resolved, &viewer, &resolver);
        assert!(
            !r2.has_conflict(),
            "ordering the embeds clears the layout conflict"
        );
        assert_eq!(r2.embedded_cells(), vec![f1, f2], "both, now in order");
    }

    // ── §2.2: a Pin::At embed pins an immutable child version (never rots) ────

    #[test]
    fn pinned_embed_is_stable_choice() {
        let fig = CellId(0xF1);
        let eid = embed_id(1, fig);
        let mut layout = LayoutGraph::new();
        layout.apply_patch(
            Author(1),
            &[Op::Embed {
                id: eid,
                child: ChildRef::pinned(fig, 42),
                after: root(),
                role: EmbedRole::Figure,
            }],
        );
        assert_eq!(
            layout.effective_pin(eid),
            Some(Pin::At(42)),
            "the embed pins v42"
        );
        // A live embed has no fixed pin (tracks the tip).
        let mut live = LayoutGraph::new();
        live.apply_patch(
            Author(1),
            &[Op::Embed {
                id: eid,
                child: ChildRef::live(fig),
                after: root(),
                role: EmbedRole::Figure,
            }],
        );
        assert_eq!(
            live.effective_pin(eid),
            Some(Pin::Live),
            "a live embed tracks the tip"
        );
    }

    // ── recursion: a child that itself composes a grandchild ─────────────────

    #[test]
    fn composition_recurses_into_grandchildren() {
        let section = CellId(0x5EC);
        let fig = CellId(0xF1);

        // The section cell embeds the figure cell.
        let mut section_layout = LayoutGraph::new();
        section_layout.apply_patch(
            Author(2),
            &[Op::Embed {
                id: embed_id(1, fig),
                child: ChildRef::live(fig),
                after: root(),
                role: EmbedRole::Figure,
            }],
        );

        // The parent embeds the section.
        let mut parent = LayoutGraph::new();
        parent.apply_patch(
            Author(1),
            &[Op::Embed {
                id: embed_id(1, section),
                child: ChildRef::live(section),
                after: root(),
                role: EmbedRole::Section,
            }],
        );

        let resolver = MapResolver::default()
            .with(section, section_layout)
            .with(fig, leaf_cell("the figure"));
        let viewer = Viewer::able([section, fig]);
        let r = content_composed(&parent, &viewer, &resolver);

        // Top level: the section embed, rendered; inside it, the figure embed.
        match &r.segments[0] {
            Segment::Embedded {
                resolution: ChildResolution::Rendered(inner),
                child: ChildRef::Cell(c, _),
                ..
            } => {
                assert_eq!(*c, section);
                assert_eq!(
                    inner.embedded_cells(),
                    vec![fig],
                    "the grandchild figure is composed"
                );
            }
            other => panic!("expected a rendered section, got {other:?}"),
        }
    }

    // ── §6: THE DESKTOP AS A COMPOSED DOCUMENT (the reflexive weld) ───────────
    //
    // These exercise the REAL composition fold (`content_composed`) over a live
    // workspace projected through `scene_to_composed` — not a fixture. The
    // workspace IS a graph of cells: each window an `Op::Embed` of its owner.

    fn win(tag: u128, z: i64) -> DesktopSurface {
        DesktopSurface::new(CellId(tag), z)
    }

    // (POSITIVE) The live workspace projects to a composed document that ROUND-TRIPS:
    // each window's owner cell resolves through the fold, in paint (z) order.
    #[test]
    fn the_workspace_projects_to_a_composed_document_that_round_trips() {
        let surfaces = vec![win(0xA1, 0), win(0xB2, 1).focused(), win(0xC3, 2)];
        let layout = scene_to_composed(&surfaces, Author(1));
        let resolver = workspace_resolver(&surfaces);
        // The viewer holds every window's owner cap (a full-authority desktop).
        let viewer = Viewer::able(surfaces.iter().map(|s| s.owner));

        let r = content_composed(&layout, &viewer, &resolver);
        // ROUND-TRIP: the embedded cells are exactly the window owners, IN z-ORDER.
        assert_eq!(
            r.embedded_cells(),
            vec![CellId(0xA1), CellId(0xB2), CellId(0xC3)],
            "the composed desktop embeds each window's owner cell in paint order"
        );
        assert!(
            !r.has_conflict(),
            "a single-author desktop layout is conflict-free"
        );
        assert!(
            !r.has_darkened(),
            "a full-authority viewer reads every window"
        );
        // The embedded surfaces RESOLVE (the fold recursed into each window's cell).
        for seg in &r.segments {
            if let Segment::Embedded { resolution, .. } = seg {
                assert!(
                    matches!(resolution, ChildResolution::Rendered(_)),
                    "each window resolves to a rendered child, got {resolution:?}"
                );
            }
        }
    }

    // (EDITING DRIVES A WORKSPACE CHANGE) Closing a window is an `Op::Remove` on the
    // projected layout — a REAL layout edit through the embed grammar — and the
    // re-folded desktop no longer embeds that window. The reflexive loop: the
    // document editor editing the document that IS the desktop.
    #[test]
    fn editing_the_projected_document_drives_a_real_workspace_change() {
        let surfaces = vec![win(0xA1, 0), win(0xB2, 1), win(0xC3, 2)];
        let mut layout = scene_to_composed(&surfaces, Author(1));
        let resolver = workspace_resolver(&surfaces);
        let viewer = Viewer::able(surfaces.iter().map(|s| s.owner));

        // Before: three windows.
        let before = content_composed(&layout, &viewer, &resolver);
        assert_eq!(before.embedded_cells().len(), 3);

        // EDIT: close the middle window (an Op::Remove authored on the layout).
        layout.apply_patch(Author(1), &[close_surface(&surfaces[1])]);
        let after = content_composed(&layout, &viewer, &resolver);
        assert_eq!(
            after.embedded_cells(),
            vec![CellId(0xA1), CellId(0xC3)],
            "the closed window drops off the desktop; the order conducts through it"
        );

        // REORDER: place C3 before A1 (an Op::Order — the layout resolution primitive),
        // and the reordered desktop still embeds both surviving windows.
        let a1 = surface_embed_id(&surfaces[0]);
        let c3 = surface_embed_id(&surfaces[2]);
        layout.apply_patch(Author(2), &[Op::Order { from: c3, to: a1 }]);
        let reordered = content_composed(&layout, &viewer, &resolver);
        assert_eq!(
            reordered.embedded_cells().len(),
            2,
            "the reorder edit kept both windows"
        );
    }

    // (NEGATIVE) An OUT-OF-CAP window DARKENS — the per-viewer membrane through the
    // REAL fold. A viewer who lacks one window's owner cap sees that window darkened
    // (provenance/citation kept, content withheld), never forged, while the rest of
    // the desktop stays usable. This is the firmament fog-of-war on the desktop.
    #[test]
    fn an_out_of_cap_window_darkens_in_the_composed_desktop() {
        let surfaces = vec![win(0xA1, 0), win(0x5EC, 1), win(0xC3, 2)];
        let layout = scene_to_composed(&surfaces, Author(1));
        let resolver = workspace_resolver(&surfaces);
        // The viewer holds A1 and C3, but NOT the secret window 0x5EC.
        let viewer = Viewer::able([CellId(0xA1), CellId(0xC3)]);

        let r = content_composed(&layout, &viewer, &resolver);
        assert!(r.has_darkened(), "the out-of-cap window darkens");
        // The citation (which cell) survives for ALL three; only the secret's bytes
        // are withheld.
        assert_eq!(
            r.embedded_cells(),
            vec![CellId(0xA1), CellId(0x5EC), CellId(0xC3)],
            "every window's citation survives (the secret is darkened, not erased)"
        );
        // Exactly the secret window darkened; the readable two rendered.
        for seg in &r.segments {
            if let Segment::Embedded {
                resolved_cell: Some(cell),
                resolution,
                ..
            } = seg
            {
                if *cell == CellId(0x5EC) {
                    assert!(
                        matches!(resolution, ChildResolution::Darkened { .. }),
                        "the out-of-cap window is darkened"
                    );
                } else {
                    assert!(
                        matches!(resolution, ChildResolution::Rendered(_)),
                        "the in-cap windows render"
                    );
                }
            }
        }

        // A viewer WITH the secret cap sees the whole desktop — the membrane is the
        // only gate (no window is darkened by anything but caps).
        let cleared = Viewer::able(surfaces.iter().map(|s| s.owner));
        assert!(
            !content_composed(&layout, &cleared, &resolver).has_darkened(),
            "a fully-capped viewer reads every window"
        );
    }

    // ── §2: the NAMED INTERLEAVE POINT, now CLOSED (text is no longer skipped) ─

    #[test]
    fn text_layout_atoms_are_interleaved_not_skipped() {
        // A composed layout whose parent carries its OWN text run BEFORE an embed.
        // The prototype used to skip text (composition.rs:941-947, "the named
        // interleave point"); the fold now emits it in document order.
        let fig = CellId(0xF1);
        let mut layout = LayoutGraph::new();
        // A parent text atom right after ROOT.
        let tid = AtomId::derive(1234, "intro");
        layout.insert_atom(LayoutAtom {
            id: tid,
            content: AtomContent::Text("Introduction. ".to_string()),
            status: Status::Alive,
            provenance: Provenance {
                author: Author(1),
                patch: crate::atom::PatchId(1),
            },
        });
        layout.connect_pub(AtomId::ROOT, tid);
        // Then an embed of the figure, ordered after the text.
        let eid = embed_id(1, fig);
        layout.apply_patch(
            Author(1),
            &[Op::Embed {
                id: eid,
                child: ChildRef::live(fig),
                after: tid,
                role: EmbedRole::Figure,
            }],
        );

        let viewer = Viewer::able([fig]);
        let resolver = MapResolver::default().with(fig, leaf_cell("a figure"));
        let r = content_composed(&layout, &viewer, &resolver);

        // The parent's text run is PRESENT (previously dropped) and ordered before
        // the embed.
        let texts: Vec<&str> = r
            .segments
            .iter()
            .filter_map(|s| match s {
                Segment::Text(t) => Some(t.as_str()),
                _ => None,
            })
            .collect();
        assert_eq!(
            texts,
            vec!["Introduction. "],
            "the parent's text run is interleaved, not skipped"
        );
        assert_eq!(r.embedded_cells(), vec![fig], "the embed still resolves");
        match (&r.segments[0], &r.segments[1]) {
            (Segment::Text(t), Segment::Embedded { .. }) => {
                assert_eq!(t, "Introduction. ", "text comes first, in document order")
            }
            other => panic!("expected text then embed, got {other:?}"),
        }
    }

    // (FORKABLE) Two devices each add a different window concurrently => the layout
    // pushout merges both, and a genuine same-position fork is a first-class layout
    // conflict (the desktop is mergeable/forkable through the SAME pushout a prose
    // document is).
    #[test]
    fn two_devices_each_open_a_window_merge_as_a_layout_pushout() {
        let base_surfaces = vec![win(0xA1, 0)];
        let base = scene_to_composed(&base_surfaces, Author(1));
        let a1 = surface_embed_id(&base_surfaces[0]);

        // Device 1 opens window B after A.
        let mut d1 = base.clone();
        d1.apply_patch(
            Author(1),
            &[Op::Embed {
                id: surface_embed_id(&win(0xB2, 1)),
                child: ChildRef::live(CellId(0xB2)),
                after: a1,
                role: EmbedRole::Section,
            }],
        );
        // Device 2 opens window C after A (concurrently — same anchor, no order).
        let mut d2 = base.clone();
        d2.apply_patch(
            Author(2),
            &[Op::Embed {
                id: surface_embed_id(&win(0xC3, 1)),
                child: ChildRef::live(CellId(0xC3)),
                after: a1,
                role: EmbedRole::Section,
            }],
        );

        let merged = merge_layout(&d1, &d2);
        let all = vec![win(0xA1, 0), win(0xB2, 1), win(0xC3, 2)];
        let resolver = workspace_resolver(&all);
        let viewer = Viewer::able([CellId(0xA1), CellId(0xB2), CellId(0xC3)]);
        let r = content_composed(&merged, &viewer, &resolver);
        // Both devices' windows opened at the same position (a fork) — surfaced as a
        // first-class layout conflict, never silently lost.
        assert!(
            r.has_conflict(),
            "two windows opened at the same position are a first-class layout fork"
        );
        let conflict = r
            .segments
            .iter()
            .any(|s| matches!(s, Segment::LayoutConflict { .. }));
        assert!(
            conflict,
            "the desktop renders the contended window placement honestly"
        );
    }
}
