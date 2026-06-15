//! The **dreggverse navigation** — "what links here", made a real, verifiable,
//! per-viewer query on the witness-graph.
//!
//! Ted Nelson's grievance with the web was the **one-way link**: a page points
//! OUT, but nothing points back, so "what links here" is unanswerable except by a
//! search engine's best-effort crawl. Xanadu wanted **two-way links** — navigable
//! in both directions, never dangling. The web never delivered them, because in an
//! ambient-authority world the back-link is a hand-maintained index that drifts.
//!
//! dregg already ships the missing half: [`Backlinks`] (the
//! `starbridge_web_surface::transclusion` primitive, the Rust mirror of
//! `Dregg2.Deos.Transclusion`) renders the witness-graph the *other* way — "who
//! transcludes / observes me" — and each backlink carries the cited receipt +
//! content commitment, so it is a **verifiable fact** ("observer O quoted source S's
//! value V at receipt R"), not a pointer that can dangle. This module NAMES that as
//! the navigable docuverse map Nelson wanted, and adds the two moves a *map* needs
//! over a single backlink readout — reinventing nothing:
//!
//! 1. **the direct backlinks** — [`DreggverseMap::links_to`] is exactly the REAL
//!    [`Backlinks::observers_of`]: given a cell, who transcludes/observes it. The
//!    two-way link, one hop.
//! 2. **the transitive docuverse map** — [`DreggverseMap::transitive_map`] follows
//!    the link graph: an observer is itself a cell that may be observed, so it walks
//!    `observers_of(observer)` outward, **bounded by `depth`**, yielding the
//!    [`DreggverseGraph`] — the nodes reachable as backlinks-of-backlinks and the
//!    directed `observer → source` edges between them (each carrying the cited
//!    receipt + content commitment from the underlying [`Observer`]). The map is
//!    cycle-safe (a cell is expanded once) and depth-bounded (no runaway crawl).
//! 3. **the per-viewer membrane (fog-of-war for links)** —
//!    [`DreggverseMap::project_for`] projects the map through the REAL starbridge
//!    [`Membrane`]: a backlink whose **link lineage** the viewer's held authority
//!    cannot admit (the membrane's [`Membrane::project`] refuses — incomparable or
//!    insufficient authority, the proven `is_attenuation` lattice) is **OMITTED**.
//!    Two viewers navigating "the same" docuverse see DIFFERENT maps — each sees only
//!    the links its capabilities authorize. The membrane makes the docuverse
//!    *relational*, exactly as it makes rehydration relational.
//!
//! Everything here drives the REAL primitives — [`Backlinks`] / [`Observer`] for the
//! graph, [`Membrane`] / [`SurfaceCapability`] for the projection (the SAME lattice
//! [`crate::transclude_affordance`] and `rehydrate` use). No parallel backlink index,
//! no parallel cap model, no toy graph. The witness-graph IS the docuverse; this is
//! its navigation.
//!
//! ## Cockpit follow-on (named, NOT built here)
//!
//! - **the "what links here" panel** — a starbridge-cockpit side-panel that, for the
//!   cell currently in focus, renders [`DreggverseMap::transitive_map`] projected
//!   through the focused agent's membrane ([`DreggverseMap::project_for`]): the
//!   backlinks the agent is authorized to see, each a clickable navigation into the
//!   observing cell (and recursively *its* "what links here"). The cockpit owns the
//!   render + the click-to-navigate; this module owns the verified, per-viewer graph
//!   it renders. (A different lane owns `starbridge-v2`; this names the seam, it does
//!   not reach into it.)

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use starbridge_web_surface::delegate::SurfaceCapability;
use starbridge_web_surface::rehydrate::Membrane;
use starbridge_web_surface::transclusion::{Backlinks, Observer};

use dregg_types::CellId;

// =============================================================================
// DreggverseLink — one directed, verifiable backlink edge (observer → source)
// =============================================================================

/// One **directed backlink edge** in the docuverse map: `observer` transcludes /
/// observes `source`, cited at the receipt the observation was pinned to.
///
/// This is the navigable form of one [`Observer`] record from the REAL
/// [`Backlinks`]: it adds the `source` end (the [`Observer`] is stored keyed by
/// source, so the source is implicit there; here the edge is self-describing for the
/// map). The `receipt_hash` + `content_hash` are carried straight from the
/// [`Observer`] — so the edge is a **verifiable fact** ("observer O quoted source S's
/// value V at receipt R"), the two-way link Nelson wanted, finally honest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DreggverseLink {
    /// The cell that transcludes/observes — the *source* end of the navigation arrow
    /// "what links here points back FROM".
    pub observer: CellId,
    /// The cell being transcluded/observed — the *target* the backlink points AT.
    pub source: CellId,
    /// The receipt the observation was pinned to (the cited immutable past — what
    /// makes the backlink datable + verifiable, not a bare pointer).
    pub receipt_hash: [u8; 32],
    /// The source content commitment that was observed (what value was quoted).
    pub content_hash: [u8; 32],
}

impl DreggverseLink {
    /// Lift one [`Observer`] of `source` into a self-describing edge.
    fn from_observer(source: CellId, obs: &Observer) -> Self {
        DreggverseLink {
            observer: obs.observer,
            source,
            receipt_hash: obs.receipt_hash,
            content_hash: obs.content_hash,
        }
    }
}

// =============================================================================
// DreggverseGraph — the transitive "what links here" map
// =============================================================================

/// The **transitive docuverse map** rooted at a cell: the nodes reachable by
/// following backlinks outward (backlinks-of-backlinks, depth-bounded) and the
/// directed `observer → source` edges between them.
///
/// A [`DreggverseMap::transitive_map`] result. The `root` is the cell the question
/// "what links here" was asked of; `edges` are every backlink reached within the
/// depth bound, each a verifiable [`DreggverseLink`]; `nodes` is every cell that
/// appears (root + every observer + every intermediate source). Navigation tooling
/// renders this as the clickable backlink tree.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct DreggverseGraph {
    /// The cell the map is rooted at — the target of the "what links here" query.
    pub root: CellId,
    /// Every directed backlink edge reached within the depth bound (deduplicated,
    /// sorted for determinism). An edge `observer → source` means "observer
    /// transcludes source".
    pub edges: Vec<DreggverseLink>,
    /// Every cell appearing in the map (the root plus every endpoint of every edge)
    /// — the navigable nodes (sorted).
    pub nodes: BTreeSet<CellId>,
}

impl DreggverseGraph {
    /// An empty map rooted at `root` (its only node is the root itself — a cell
    /// nobody transcludes has no backlinks, an empty readout, never an error).
    fn empty(root: CellId) -> Self {
        let mut nodes = BTreeSet::new();
        nodes.insert(root);
        DreggverseGraph {
            root,
            edges: Vec::new(),
            nodes,
        }
    }

    /// The backlink edges pointing AT `cell` within this map (the direct "what links
    /// here" of `cell`, as captured by the transitive walk).
    pub fn edges_into(&self, cell: CellId) -> Vec<&DreggverseLink> {
        self.edges.iter().filter(|e| e.source == cell).collect()
    }

    /// The observer cells that transclude `cell` within this map (the cells "what
    /// links here" would list for `cell`).
    pub fn observers_of(&self, cell: CellId) -> Vec<CellId> {
        let mut v: Vec<CellId> = self
            .edges
            .iter()
            .filter(|e| e.source == cell)
            .map(|e| e.observer)
            .collect();
        v.sort();
        v.dedup();
        v
    }

    /// How many backlink edges the map carries (the docuverse's reach from the
    /// root within the depth bound — a measure of how deeply the value is quoted).
    pub fn link_count(&self) -> usize {
        self.edges.len()
    }

    /// Is the map empty of backlinks (the root is transcluded by nobody reachable)?
    pub fn is_empty(&self) -> bool {
        self.edges.is_empty()
    }
}

// =============================================================================
// DreggverseMap — the navigable backlink index, built ON the real Backlinks
// =============================================================================

/// The **dreggverse navigation** — Nelson's two-way docuverse, browsable.
///
/// Wraps the REAL [`Backlinks`] witness-graph readout and adds per-source **link
/// lineages** (the authority a viewer must be able to project to SEE a backlink, the
/// fog-of-war). It answers three queries:
///
/// - [`Self::links_to`] — the direct backlinks of a cell (the REAL
///   [`Backlinks::observers_of`]).
/// - [`Self::transitive_map`] — the depth-bounded backlinks-of-backlinks graph.
/// - [`Self::project_for`] — the same, projected through a viewer's [`Membrane`]:
///   a backlink the viewer cannot project is OMITTED.
///
/// It owns no parallel backlink store: the graph IS the borrowed [`Backlinks`]; this
/// type adds only the navigation (transitive walk) and the membrane (per-viewer fog).
#[derive(Clone, Debug)]
pub struct DreggverseMap<'a> {
    /// The REAL witness-graph readout — "who transcludes/observes whom". Borrowed:
    /// the map is a *view* over the live backlinks, never a copy that can drift.
    links: &'a Backlinks,
    /// Per-source **link lineage**: the authority a viewer must be able to project
    /// (through its [`Membrane`]) to be shown the backlinks of that source — the
    /// link's fog-of-war ceiling. A source with no entry here is **public** (every
    /// viewer sees its backlinks); a source with a lineage is gated, and a viewer
    /// whose held authority the membrane cannot meet with the lineage does not see
    /// those backlinks ([`Self::project_for`]).
    link_lineage: BTreeMap<CellId, SurfaceCapability>,
}

impl<'a> DreggverseMap<'a> {
    /// Build a navigation over the REAL [`Backlinks`] witness-graph. By default every
    /// backlink is public (no lineage gate); call [`Self::gate_source`] to attach a
    /// link lineage that the per-viewer membrane must clear.
    pub fn new(links: &'a Backlinks) -> Self {
        DreggverseMap {
            links,
            link_lineage: BTreeMap::new(),
        }
    }

    /// **Gate a source's backlinks behind a link lineage** — the fog-of-war ceiling.
    ///
    /// After this, [`Self::project_for`] shows the backlinks of `source` only to a
    /// viewer whose [`Membrane`] can project `lineage` (the REAL
    /// [`Membrane::project`] meet succeeds — the viewer's held authority is comparable
    /// to and not amplifying beyond the lineage). A viewer the membrane refuses does
    /// not see these backlinks at all (they are omitted from its map). Returns `self`
    /// for chaining.
    pub fn gate_source(mut self, source: CellId, lineage: SurfaceCapability) -> Self {
        self.link_lineage.insert(source, lineage);
        self
    }

    /// The link lineage gating a source's backlinks, if any (none = public).
    pub fn lineage_of(&self, source: CellId) -> Option<&SurfaceCapability> {
        self.link_lineage.get(&source)
    }

    /// **"What links here?"** — the direct backlinks of `cell`: the observers that
    /// transclude/observe it, straight from the REAL [`Backlinks::observers_of`].
    ///
    /// This is the two-way link, one hop: the reverse of "what does this cell quote"
    /// is "what quotes this cell". Empty if nobody transcludes it (an empty readout,
    /// never an error). The returned [`Observer`] slice carries each backlink's cited
    /// receipt + content commitment (the verifiable fact).
    pub fn links_to(&self, cell: CellId) -> &[Observer] {
        self.links.observers_of(cell)
    }

    /// The direct backlinks of `cell` as self-describing [`DreggverseLink`] edges
    /// (the same data as [`Self::links_to`], lifted to navigable edges with both
    /// endpoints named).
    pub fn direct_edges(&self, cell: CellId) -> Vec<DreggverseLink> {
        self.links
            .observers_of(cell)
            .iter()
            .map(|obs| DreggverseLink::from_observer(cell, obs))
            .collect()
    }

    /// How many distinct observers transclude `cell` — the in-degree in the docuverse
    /// witness-graph (delegates to the REAL [`Backlinks::backlink_count`]).
    pub fn backlink_count(&self, cell: CellId) -> usize {
        self.links.backlink_count(cell)
    }

    /// **The transitive docuverse map** — follow backlinks outward from `cell` up to
    /// `depth` hops, building the [`DreggverseGraph`] of every backlink reached.
    ///
    /// `depth` is the hop bound: `depth = 1` is exactly the direct backlinks of
    /// `cell`; `depth = 2` adds the backlinks of each of those observers (who links to
    /// the things that link here); and so on. The walk is a breadth-first expansion
    /// over the witness-graph:
    ///
    /// - **cycle-safe** — each cell is expanded at most once (a transclusion cycle
    ///   A→B→A does not loop forever);
    /// - **depth-bounded** — no cell beyond `depth` hops is expanded (no runaway
    ///   crawl — the docuverse map is always finite + cheap);
    /// - **deterministic** — edges + nodes are sorted, so the map is reproducible.
    ///
    /// `depth = 0` yields just the root node with no edges (the degenerate "look but
    /// take no hops" map). A cell nobody transcludes yields an empty map (root only).
    pub fn transitive_map(&self, cell: CellId, depth: usize) -> DreggverseGraph {
        self.walk(cell, depth, |_source| true)
    }

    /// **Project the transitive map PER-VIEWER through the membrane** — the
    /// fog-of-war for links.
    ///
    /// Walks the same transitive backlink graph as [`Self::transitive_map`], but a
    /// source whose backlinks are GATED (a [`Self::gate_source`] link lineage) is
    /// included **only if** the `viewer` membrane can project that lineage — the REAL
    /// [`Membrane::project`]: the viewer's held authority must meet the lineage
    /// (comparable, never amplifying, via the proven `is_attenuation` lattice). If the
    /// membrane refuses, that source's backlinks are **OMITTED** from this viewer's
    /// map (and so is any deeper structure reachable only through them — you cannot
    /// navigate a link you cannot see).
    ///
    /// An UNGATED source is public: every viewer sees its backlinks. Two viewers thus
    /// navigate DIFFERENT maps of the same docuverse — each sees only the links its
    /// capabilities authorize. This is the membrane made navigational.
    pub fn project_for(&self, cell: CellId, depth: usize, viewer: &Membrane) -> DreggverseGraph {
        self.walk(cell, depth, |source| self.viewer_may_see(source, viewer))
    }

    /// Is `viewer` authorized to see the backlinks of `source`?
    ///
    /// An ungated source is public (`true`). A gated source is visible iff the
    /// `viewer` membrane can project its link lineage through the REAL
    /// [`Membrane::project`] — i.e. the viewer's held authority meets the lineage
    /// without amplifying (the proven lattice). A membrane refusal
    /// (incomparable/insufficient authority) is the fog: `false`, the backlink is
    /// omitted.
    pub fn viewer_may_see(&self, source: CellId, viewer: &Membrane) -> bool {
        match self.link_lineage.get(&source) {
            None => true, // public: no lineage gate.
            Some(lineage) => viewer.project(lineage).is_ok(),
        }
    }

    /// The shared BFS: expand backlinks outward from `root` up to `depth` hops,
    /// including a source's backlinks only when `admit(source)` holds (the
    /// per-viewer fog predicate — always-true for the unprojected map). Cycle-safe
    /// (each cell expanded once), depth-bounded, deterministic.
    fn walk(&self, root: CellId, depth: usize, admit: impl Fn(CellId) -> bool) -> DreggverseGraph {
        let mut graph = DreggverseGraph::empty(root);
        if depth == 0 {
            return graph;
        }

        // Frontier of (cell, hops-from-root-so-far). We expand a cell's backlinks
        // (the cells that transclude IT) when its remaining budget allows.
        let mut seen: BTreeSet<CellId> = BTreeSet::new();
        let mut queue: VecDeque<(CellId, usize)> = VecDeque::new();
        seen.insert(root);
        queue.push_back((root, 0));

        let mut edges: BTreeSet<DreggverseLink> = BTreeSet::new();

        while let Some((cell, hops)) = queue.pop_front() {
            if hops >= depth {
                continue; // out of hop budget — do not expand further.
            }
            // The fog: a viewer who cannot see this source's backlinks gets none of
            // them (and cannot navigate deeper through them).
            if !admit(cell) {
                continue;
            }
            for obs in self.links.observers_of(cell) {
                let link = DreggverseLink::from_observer(cell, obs);
                graph.nodes.insert(link.observer);
                graph.nodes.insert(link.source);
                edges.insert(link);
                // Enqueue the observer to expand ITS backlinks (one hop deeper).
                if seen.insert(obs.observer) {
                    queue.push_back((obs.observer, hops + 1));
                }
            }
        }

        graph.edges = edges.into_iter().collect();
        graph.edges.sort();
        graph
    }
}

// `DreggverseLink` needs a total order so the BFS can dedup + the map is
// deterministic. Order by (source, observer, receipt, content) — a stable,
// content-derived key (no semantic meaning, just reproducibility).
impl PartialOrd for DreggverseLink {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for DreggverseLink {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.source
            .cmp(&other.source)
            .then(self.observer.cmp(&other.observer))
            .then(self.receipt_hash.cmp(&other.receipt_hash))
            .then(self.content_hash.cmp(&other.content_hash))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::AuthRequired;
    use starbridge_web_surface::transclusion::TranscludedField;
    use starbridge_web_surface::web_of_cells::WebOfCells;

    fn cid(b: u8) -> CellId {
        CellId::from_bytes([b; 32])
    }

    /// Publish a source document into a fresh web-of-cells and resolve a genuine
    /// transclusion of it — the SAME helper shape the primitive's own tests use (a
    /// real 3-of-3-attested finalized read), so every backlink we record carries a
    /// genuine cited receipt + content commitment.
    fn quote_of(seed: u8, body: &[u8]) -> TranscludedField {
        let mut web = WebOfCells::new(3);
        let uri = web.publish(seed, body, "dregg://source-doc");
        TranscludedField::include(&web, &uri).expect("transclusion resolves")
    }

    /// The source cell a resolved quote points at (the backlink target).
    fn source_of(quote: &TranscludedField) -> CellId {
        quote.provenance.source.cell
    }

    // (1) A CELL'S DIRECT BACKLINKS ENUMERATE — "what links here", one hop, straight
    //     from the REAL Backlinks::observers_of.
    #[test]
    fn direct_backlinks_enumerate() {
        let quote = quote_of(1, b"<h1>widely-quoted source</h1>");
        let source = source_of(&quote);

        // Three observer documents transclude the same source.
        let mut links = Backlinks::new();
        let (obs_a, obs_b, obs_c) = (cid(101), cid(102), cid(103));
        links.observe(obs_a, &quote);
        links.observe(obs_b, &quote);
        links.observe(obs_c, &quote);

        let map = DreggverseMap::new(&links);

        // links_to is the REAL observers_of: exactly the three observers.
        let observers = map.links_to(source);
        assert_eq!(observers.len(), 3, "three observers transclude the source");
        let names: Vec<CellId> = observers.iter().map(|o| o.observer).collect();
        assert!(names.contains(&obs_a) && names.contains(&obs_b) && names.contains(&obs_c));
        assert_eq!(map.backlink_count(source), 3);

        // The navigable edge form names both endpoints + carries the verifiable
        // receipt/content from the underlying Observer.
        let edges = map.direct_edges(source);
        assert_eq!(edges.len(), 3);
        assert!(edges.iter().all(|e| e.source == source));
        assert!(edges
            .iter()
            .all(|e| e.receipt_hash == quote.provenance.receipt_hash));
        assert!(edges
            .iter()
            .all(|e| e.content_hash == quote.provenance.content_hash));
    }

    // (2) THE TRANSITIVE MAP AT DEPTH 2 — backlinks-of-backlinks. A→B (B transcludes
    //     A), B→C (C transcludes B): "what links here" for A at depth 2 reaches C.
    #[test]
    fn transitive_map_at_depth_two() {
        // Build a real chain of quotes. Cell A is the deep source; B transcludes A;
        // C transcludes B. (We use distinct published sources so each quote is a
        // genuine finalized read; the OBSERVER ids are what wire the chain.)
        let quote_a = quote_of(10, b"<h1>A: the root source</h1>");
        let quote_b = quote_of(11, b"<h1>B: quotes A</h1>");
        let a = source_of(&quote_a); // the cell everyone's question is about
        let b = source_of(&quote_b);
        let c = cid(120);

        let mut links = Backlinks::new();
        // B transcludes A  → backlink A ← B.
        links.observe(b, &quote_a);
        // C transcludes B  → backlink B ← C.
        links.observe(c, &quote_b);

        let map = DreggverseMap::new(&links);

        // DEPTH 1: "what links here" for A is just B (the direct backlink).
        let d1 = map.transitive_map(a, 1);
        assert_eq!(d1.observers_of(a), vec![b]);
        assert_eq!(d1.link_count(), 1, "depth 1 = direct backlinks only");
        assert!(!d1.nodes.contains(&c), "C is two hops out — not at depth 1");

        // DEPTH 2: the map now reaches C (who links to B, who links to A).
        let d2 = map.transitive_map(a, 2);
        assert_eq!(d2.root, a);
        assert_eq!(d2.link_count(), 2, "two edges: A<-B and B<-C");
        assert_eq!(d2.observers_of(a), vec![b], "B still the direct backlink of A");
        assert_eq!(d2.observers_of(b), vec![c], "C is the backlink of B (the 2nd hop)");
        // Every node of the transitive docuverse appears.
        assert!(d2.nodes.contains(&a) && d2.nodes.contains(&b) && d2.nodes.contains(&c));
        // The edges are the two verifiable backlinks, both endpoints named.
        assert!(d2
            .edges
            .iter()
            .any(|e| e.source == a && e.observer == b));
        assert!(d2
            .edges
            .iter()
            .any(|e| e.source == b && e.observer == c));
    }

    // (2b) THE TRANSITIVE WALK IS CYCLE-SAFE + DEPTH-BOUNDED — a transclusion cycle
    //      does not loop forever, and depth 0 is the degenerate root-only map.
    #[test]
    fn transitive_walk_is_cycle_safe_and_bounded() {
        // A cycle: B transcludes A AND A transcludes B (a real quoting cycle).
        let quote_a = quote_of(20, b"<h1>A</h1>");
        let quote_b = quote_of(21, b"<h1>B</h1>");
        let a = source_of(&quote_a);
        let b = source_of(&quote_b);

        let mut links = Backlinks::new();
        links.observe(b, &quote_a); // A <- B
        links.observe(a, &quote_b); // B <- A  (the cycle)

        let map = DreggverseMap::new(&links);

        // A deep walk terminates (cycle-safe: each cell expanded once) and finds both
        // edges, no more.
        let g = map.transitive_map(a, 99);
        assert_eq!(g.link_count(), 2, "the cycle yields exactly its two edges, no loop");
        assert!(g.nodes.contains(&a) && g.nodes.contains(&b));

        // depth 0 is the degenerate look-but-take-no-hops map: root only, no edges.
        let g0 = map.transitive_map(a, 0);
        assert!(g0.is_empty());
        assert_eq!(g0.nodes.len(), 1);
        assert!(g0.nodes.contains(&a));
    }

    // (3) A PER-VIEWER PROJECTION OMITS UNAUTHORIZED LINKS — the fog-of-war. A gated
    //     source's backlinks are visible only to a viewer whose membrane can project
    //     the link lineage; a weaker/incomparable viewer sees them OMITTED.
    #[test]
    fn per_viewer_projection_omits_unauthorized_links() {
        let quote = quote_of(30, b"<h1>a gated source</h1>");
        let source = source_of(&quote);

        let mut links = Backlinks::new();
        let observer = cid(140);
        links.observe(observer, &quote);

        // Gate the source's backlinks behind a strong (Either) link lineage over the
        // source cell — only a viewer whose membrane can project Either sees them.
        let lineage = SurfaceCapability::root(source, AuthRequired::Either);
        let map = DreggverseMap::new(&links).gate_source(source, lineage);

        // An AUTHORIZED viewer (holds Either) projects the lineage → sees the backlink.
        let strong = Membrane::new(SurfaceCapability::root(cid(150), AuthRequired::Either));
        assert!(map.viewer_may_see(source, &strong));
        let strong_map = map.project_for(source, 2, &strong);
        assert_eq!(strong_map.observers_of(source), vec![observer]);
        assert_eq!(strong_map.link_count(), 1, "authorized viewer sees the backlink");

        // An UNAUTHORIZED viewer whose authority is INCOMPARABLE to the lineage: a
        // Signature lineage vs a Proof viewer — neither attenuates the other, so the
        // membrane REFUSES the projection (the same incomparable-rights refusal the
        // rehydrate membrane proves). An incomparable viewer is fogged.
        let sig_lineage = SurfaceCapability::root(source, AuthRequired::Signature);
        let map2 = DreggverseMap::new(&links).gate_source(source, sig_lineage);
        let incomparable = Membrane::new(SurfaceCapability::root(cid(151), AuthRequired::Proof));
        assert!(
            !map2.viewer_may_see(source, &incomparable),
            "an incomparable viewer's membrane refuses the lineage → fogged"
        );
        let fogged = map2.project_for(source, 2, &incomparable);
        assert!(
            fogged.is_empty(),
            "the unauthorized viewer sees the backlink OMITTED (fog-of-war)"
        );
        assert!(
            !fogged.nodes.contains(&observer),
            "and cannot even see the observing cell"
        );

        // The SAME map is relational: the unprojected (god's-eye) map still has it.
        assert_eq!(map2.transitive_map(source, 2).link_count(), 1);
    }

    // (3b) AN UNGATED SOURCE IS PUBLIC — every viewer sees its backlinks, even a weak
    //      one (no lineage gate = no fog).
    #[test]
    fn an_ungated_source_is_public_to_every_viewer() {
        let quote = quote_of(40, b"<h1>a public source</h1>");
        let source = source_of(&quote);
        let mut links = Backlinks::new();
        let observer = cid(160);
        links.observe(observer, &quote);

        // No gate_source call → public.
        let map = DreggverseMap::new(&links);
        // Even the weakest viewer sees the backlink (no lineage to clear).
        let weak = Membrane::new(SurfaceCapability::root(cid(161), AuthRequired::Signature));
        assert!(map.viewer_may_see(source, &weak));
        assert_eq!(
            map.project_for(source, 1, &weak).observers_of(source),
            vec![observer]
        );
    }

    // (4) AN EMPTY CELL HAS NO BACKLINKS — a cell nobody transcludes yields an empty
    //     readout (never an error), and an empty transitive map (root only).
    #[test]
    fn an_empty_cell_has_no_backlinks() {
        let links = Backlinks::new(); // nobody has transcluded anything
        let map = DreggverseMap::new(&links);
        let lonely = cid(200);

        // Direct: empty readout.
        assert!(map.links_to(lonely).is_empty());
        assert_eq!(map.backlink_count(lonely), 0);
        assert!(map.direct_edges(lonely).is_empty());

        // Transitive: the root-only map (no edges), at any depth.
        let g = map.transitive_map(lonely, 5);
        assert!(g.is_empty());
        assert_eq!(g.nodes.len(), 1);
        assert!(g.nodes.contains(&lonely));

        // Per-viewer: still empty (nothing to fog).
        let viewer = Membrane::new(SurfaceCapability::root(cid(201), AuthRequired::Either));
        assert!(map.project_for(lonely, 3, &viewer).is_empty());
    }
}
