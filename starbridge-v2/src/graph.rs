//! THE OCAP DELEGATION GRAPH — the whole-graph capability layout (multi-hop).
//!
//! `docs/DREGG-DESKTOP-OS.md` casts the desktop as the firmament made visual:
//! "the View tree IS the ocap graph." Every other panel reflects ONE object;
//! this one reflects the *relation between* objects — the live capability graph
//! the whole image is woven from. It projects the embedded [`World`]'s c-lists
//! into a navigable whole-graph layout:
//!
//!   * **NODES** are cells (every cell in the ledger is a node — a potential
//!     grantor and grantee of authority), each carrying its live balance /
//!     lifecycle / cap count so the node renders without a second read.
//!   * **EDGES** are capability grants: a directed edge `holder ──cap──▶ target`
//!     for every `CapabilityRef` in every cell's c-list. This is the literal
//!     ocap graph — "connectivity begets connectivity" drawn as arrows. Each
//!     edge carries the rights (`AuthRequired`), the holder's slot, whether the
//!     cap is faceted (effect-restricted) or expiring, and the R7 delegation
//!     epoch snapshot (`stored_epoch`) that marks a *delegated* (vs. direct)
//!     authority — so a multi-hop delegation chain is legible as such.
//!
//! The MULTI-HOP story is the whole point. Authority in dregg is transitive
//! reach: if A holds a cap to B and B holds a cap to C, then A can (by the
//! no-amplification gate) only ever *attenuate* what it hands on — but the
//! *graph* of who-can-reach-whom is the multi-hop closure of the edges. This
//! module computes that closure ([`OcapGraph::reachable_from`], a BFS over the
//! edges) so the panel can answer "what is the full blast radius of this cell's
//! authority?" — and lay the graph out [`OcapGraph::layered_from`] in delegation
//! DEPTH layers from a chosen root (the grantor at layer 0, its direct grantees
//! at layer 1, their grantees at layer 2, …) — a true multi-hop layout, not a
//! flat adjacency dump.
//!
//! The pale-ghost question (§5) for the graph: *can an operator be fooled about
//! who can reach whom?* No — every edge is a real `CapabilityRef` read from the
//! live ledger (never a parallel model), and the reachability is the genuine
//! transitive closure of those edges. This is the cap-graph as the executor
//! actually holds it.
//!
//! gpui-free + `cargo test`-able: built purely from the [`World`]; the cockpit
//! maps [`OcapGraph`] onto the GRAPH tab (a node-link diagram), and clicking a
//! node re-roots the layered layout on it.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use dregg_cell::{AuthRequired, CellId};

use crate::world::World;

/// One node in the ocap graph — a cell, carrying the live state a node-link
/// view renders without a second ledger read.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GraphNode {
    /// The cell this node IS.
    pub cell: CellId,
    /// A short operator-legible id (abbreviated cell id).
    pub short: String,
    /// The cell's live balance (issuer wells carry −supply — render distinctly).
    pub balance: i64,
    /// The cell's lifecycle label (`live` / `sealed` / `destroyed` / …).
    pub lifecycle: String,
    /// How many OUTBOUND capability edges this node holds (its out-degree — the
    /// breadth of authority it can hand on).
    pub out_degree: usize,
    /// How many INBOUND capability edges point at this node (its in-degree — how
    /// many holders can reach it).
    pub in_degree: usize,
}

/// One directed edge in the ocap graph — a capability grant `holder ──▶ target`.
/// This is the literal ocap primitive: the holder's authority to act upon the
/// target, at `rights`, via the holder's local `slot`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GraphEdge {
    /// The cell HOLDING the capability (the grantor / the arrow's tail).
    pub holder: CellId,
    /// The cell the capability REACHES (the arrow's head).
    pub target: CellId,
    /// The holder's local c-list slot for this cap (its handle).
    pub slot: u32,
    /// The rights the holder wields over the target (the `AuthRequired` lattice).
    pub rights: AuthRequired,
    /// Whether the cap is confined to a subset of effect types (a facet).
    pub faceted: bool,
    /// An optional expiry height (the edge is invalid beyond it), if any.
    pub expires_at: Option<u64>,
    /// The R7 delegation-epoch snapshot (`stored_epoch`): `Some(e)` marks this as
    /// a DELEGATED authority (stored from a grantor at epoch `e`, re-checked for
    /// freshness at exercise); `None` is a DIRECT (self-origin) grant, exempt
    /// from the freshness re-check. This is what makes a multi-hop delegation
    /// chain legible: direct edges are origins, `stored_epoch` edges are hops.
    pub delegated_epoch: Option<u64>,
}

impl GraphEdge {
    /// A short operator-legible label for the rights ("open"/"sig"/"proof"/...).
    pub fn rights_label(&self) -> &'static str {
        rights_label(&self.rights)
    }

    /// Whether this edge is a DELEGATED authority (carries a stored epoch) vs. a
    /// direct self-origin grant. A delegation hop in a multi-hop chain.
    pub fn is_delegated(&self) -> bool {
        self.delegated_epoch.is_some()
    }
}

/// THE OCAP GRAPH — the whole-image capability layout, built from the live
/// [`World`]. Nodes are cells; edges are capability grants. gpui-free; the
/// cockpit renders it as a node-link diagram and re-roots the layered layout on
/// a clicked node.
#[derive(Clone, Debug)]
pub struct OcapGraph {
    /// Every cell in the ledger, as a node (sorted by id for a stable layout).
    nodes: Vec<GraphNode>,
    /// Every capability grant, as a directed edge.
    edges: Vec<GraphEdge>,
    /// Adjacency: holder → the set of targets it reaches directly (for BFS).
    adjacency: BTreeMap<CellId, BTreeSet<CellId>>,
}

impl OcapGraph {
    /// Build the whole ocap graph from the live world: one node per ledger cell,
    /// one edge per capability in every cell's c-list.
    pub fn build(world: &World) -> Self {
        let ledger = world.ledger();

        // First pass: edges + the adjacency map + per-node degree tallies.
        let mut edges: Vec<GraphEdge> = Vec::new();
        let mut adjacency: BTreeMap<CellId, BTreeSet<CellId>> = BTreeMap::new();
        let mut out_degree: BTreeMap<CellId, usize> = BTreeMap::new();
        let mut in_degree: BTreeMap<CellId, usize> = BTreeMap::new();

        // Iterate the ledger in id order so the graph is deterministic.
        let mut cells: Vec<(&CellId, &dregg_cell::Cell)> = ledger.iter().collect();
        cells.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));

        for (id, cell) in &cells {
            for cap in cell.capabilities.iter() {
                edges.push(GraphEdge {
                    holder: **id,
                    target: cap.target,
                    slot: cap.slot,
                    rights: cap.permissions.clone(),
                    faceted: cap.allowed_effects.is_some(),
                    expires_at: cap.expires_at,
                    delegated_epoch: cap.stored_epoch,
                });
                adjacency.entry(**id).or_default().insert(cap.target);
                *out_degree.entry(**id).or_default() += 1;
                *in_degree.entry(cap.target).or_default() += 1;
            }
        }

        // Second pass: the nodes (every ledger cell), with the degree tallies.
        let nodes: Vec<GraphNode> = cells
            .iter()
            .map(|(id, cell)| GraphNode {
                cell: **id,
                short: crate::reflect::short_hex(id.as_bytes()),
                balance: cell.state.balance(),
                lifecycle: format!("{:?}", cell.lifecycle),
                out_degree: out_degree.get(*id).copied().unwrap_or(0),
                in_degree: in_degree.get(*id).copied().unwrap_or(0),
            })
            .collect();

        OcapGraph {
            nodes,
            edges,
            adjacency,
        }
    }

    /// All nodes (cells), id-sorted.
    pub fn nodes(&self) -> &[GraphNode] {
        &self.nodes
    }

    /// All edges (capability grants).
    pub fn edges(&self) -> &[GraphEdge] {
        &self.edges
    }

    /// The number of nodes (cells) in the graph.
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// The number of edges (capability grants) in the graph.
    pub fn edge_count(&self) -> usize {
        self.edges.len()
    }

    /// The edges held BY `holder` (its outbound authority — what it can reach).
    pub fn edges_from(&self, holder: &CellId) -> Vec<&GraphEdge> {
        self.edges.iter().filter(|e| &e.holder == holder).collect()
    }

    /// The edges pointing AT `target` (its inbound authority — who can reach it).
    pub fn edges_to(&self, target: &CellId) -> Vec<&GraphEdge> {
        self.edges.iter().filter(|e| &e.target == target).collect()
    }

    /// **THE MULTI-HOP REACHABILITY** — every cell `root` can reach transitively
    /// through the capability edges (the BFS closure). This is the full blast
    /// radius of a cell's authority: A reaches B directly, and (since B's c-list
    /// can hand authority on) the *graph* of who-can-reach-whom is the transitive
    /// closure. `root` itself is NOT included (a cell trivially reaches itself).
    ///
    /// NOTE this is graph reachability (who-points-to-whom), the structural
    /// upper bound on delegation reach — the executor's no-amplification gate
    /// still bounds the *rights* handed along each hop; this is the *topology*.
    pub fn reachable_from(&self, root: &CellId) -> BTreeSet<CellId> {
        let mut seen: BTreeSet<CellId> = BTreeSet::new();
        let mut queue: VecDeque<CellId> = VecDeque::new();
        if let Some(direct) = self.adjacency.get(root) {
            for t in direct {
                if seen.insert(*t) {
                    queue.push_back(*t);
                }
            }
        }
        while let Some(node) = queue.pop_front() {
            if let Some(next) = self.adjacency.get(&node) {
                for t in next {
                    // Don't loop back through the root, and visit each once.
                    if t != root && seen.insert(*t) {
                        queue.push_back(*t);
                    }
                }
            }
        }
        seen
    }

    /// The size of the multi-hop reach from `root` (how many distinct cells its
    /// authority can transitively touch). The breadth of the blast radius.
    pub fn reach_count(&self, root: &CellId) -> usize {
        self.reachable_from(root).len()
    }

    /// **THE LAYERED MULTI-HOP LAYOUT** from a chosen `root`: a BFS partition of
    /// the reachable graph into delegation-DEPTH layers — `root` at layer 0, its
    /// DIRECT grantees at layer 1, their grantees at layer 2, and so on. This is
    /// the true multi-hop layout the GRAPH tab draws (concentric rings / columns
    /// by depth), not a flat adjacency dump: the depth of a cell is the SHORTEST
    /// delegation distance from the root, so the chain `root → a → b → c` lays out
    /// across four layers.
    ///
    /// Each layer is id-sorted for a stable render. A cell appears in exactly one
    /// layer (its shortest depth). Cells not reachable from `root` are omitted
    /// (they are a different connected component — pick another root to see them).
    pub fn layered_from(&self, root: &CellId) -> Vec<GraphLayer> {
        let mut depth: BTreeMap<CellId, usize> = BTreeMap::new();
        let mut queue: VecDeque<(CellId, usize)> = VecDeque::new();
        depth.insert(*root, 0);
        queue.push_back((*root, 0));
        while let Some((node, d)) = queue.pop_front() {
            if let Some(next) = self.adjacency.get(&node) {
                for t in next {
                    if !depth.contains_key(t) {
                        depth.insert(*t, d + 1);
                        queue.push_back((*t, d + 1));
                    }
                }
            }
        }
        // Group by depth.
        let max_depth = depth.values().copied().max().unwrap_or(0);
        let mut layers: Vec<GraphLayer> = (0..=max_depth)
            .map(|d| GraphLayer {
                depth: d,
                cells: Vec::new(),
            })
            .collect();
        let mut by_depth: Vec<Vec<CellId>> = vec![Vec::new(); max_depth + 1];
        for (cell, d) in &depth {
            by_depth[*d].push(*cell);
        }
        for (d, mut cells) in by_depth.into_iter().enumerate() {
            cells.sort_by(|a, b| a.as_bytes().cmp(b.as_bytes()));
            layers[d].cells = cells;
        }
        layers
    }

    /// Whether the graph has a directed cycle reachable from `root` through the
    /// capability edges (a *mutual* / circular delegation — A reaches B reaches
    /// A). Legible-as-such in the panel: a cycle is not a bug (mutual authority is
    /// legitimate) but it is worth surfacing — it means revocation reasoning must
    /// account for the loop.
    pub fn has_cycle_from(&self, root: &CellId) -> bool {
        // DFS with a recursion stack (gray set). Iterative to avoid deep stacks.
        let mut state: BTreeMap<CellId, u8> = BTreeMap::new(); // 0=white,1=gray,2=black
        let mut stack: Vec<(CellId, bool)> = vec![(*root, false)];
        while let Some((node, processed)) = stack.pop() {
            if processed {
                state.insert(node, 2);
                continue;
            }
            if state.get(&node).copied().unwrap_or(0) == 1 {
                continue;
            }
            state.insert(node, 1);
            stack.push((node, true));
            if let Some(next) = self.adjacency.get(&node) {
                for t in next {
                    match state.get(t).copied().unwrap_or(0) {
                        1 => return true, // back-edge to a gray node = cycle
                        2 => {}           // already finished
                        _ => stack.push((*t, false)),
                    }
                }
            }
        }
        false
    }

    /// The roots of the graph: cells with NO inbound capability edge (no holder
    /// reaches them) — the authority sources. The natural starting points for the
    /// layered layout (a treasury / operator cell that grants but is not granted).
    pub fn source_roots(&self) -> Vec<CellId> {
        let mut targeted: BTreeSet<CellId> = BTreeSet::new();
        for e in &self.edges {
            targeted.insert(e.target);
        }
        self.nodes
            .iter()
            .map(|n| n.cell)
            .filter(|c| !targeted.contains(c))
            .collect()
    }
}

/// One delegation-depth layer of the layered multi-hop layout: every cell at the
/// same shortest delegation distance from the chosen root.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GraphLayer {
    /// The delegation depth (0 = the root itself; 1 = its direct grantees; …).
    pub depth: usize,
    /// The cells at this depth (id-sorted).
    pub cells: Vec<CellId>,
}

/// A short operator-legible label for an `AuthRequired` rights value.
fn rights_label(rights: &AuthRequired) -> &'static str {
    match rights {
        AuthRequired::None => "open",
        AuthRequired::Signature => "sig",
        AuthRequired::Either => "either",
        AuthRequired::Impossible => "impossible",
        _ => "proof",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::{grant_capability, World};

    /// A world with a three-hop delegation chain: root → a → b, plus an isolated
    /// cell. Root holds a cap to `a`; `a` holds a cap to `b`. Built with the real
    /// executor (the genesis-with-cap path + legitimate grants).
    fn chain_world() -> (World, CellId, CellId, CellId, CellId) {
        let mut world = World::new();
        // b exists first (a leaf with no outbound caps).
        let b = world.genesis_cell(0xB0, 0);
        // a is born holding a cap to b.
        let (a, _a_slot) = world.genesis_cell_with_cap(0xA0, 1_000, b);
        // root is born holding a cap to a.
        let (root, _root_slot) = world.genesis_cell_with_cap(0x01, 10_000, a);
        // an isolated cell with no edges in or out.
        let iso = world.genesis_cell(0xCC, 500);
        (world, root, a, b, iso)
    }

    #[test]
    fn the_graph_has_a_node_per_cell_and_an_edge_per_cap() {
        let (world, root, a, b, _iso) = chain_world();
        let g = OcapGraph::build(&world);
        // 4 cells → 4 nodes.
        assert_eq!(g.node_count(), 4);
        // 2 capability edges: root→a, a→b.
        assert_eq!(g.edge_count(), 2);
        // The edges are the real grants.
        assert!(g.edges().iter().any(|e| e.holder == root && e.target == a));
        assert!(g.edges().iter().any(|e| e.holder == a && e.target == b));
    }

    #[test]
    fn out_and_in_degrees_match_the_cap_graph() {
        let (world, root, a, b, iso) = chain_world();
        let g = OcapGraph::build(&world);
        let node = |c: CellId| g.nodes().iter().find(|n| n.cell == c).unwrap().clone();
        // root: out 1 (→a), in 0.
        assert_eq!(node(root).out_degree, 1);
        assert_eq!(node(root).in_degree, 0);
        // a: out 1 (→b), in 1 (root→).
        assert_eq!(node(a).out_degree, 1);
        assert_eq!(node(a).in_degree, 1);
        // b: out 0, in 1 (a→).
        assert_eq!(node(b).out_degree, 0);
        assert_eq!(node(b).in_degree, 1);
        // iso: out 0, in 0.
        assert_eq!(node(iso).out_degree, 0);
        assert_eq!(node(iso).in_degree, 0);
    }

    #[test]
    fn multi_hop_reachability_is_the_transitive_closure() {
        // THE MULTI-HOP STORY: root reaches a directly AND b transitively
        // (root → a → b), even though root holds no DIRECT cap to b.
        let (world, root, a, b, iso) = chain_world();
        let g = OcapGraph::build(&world);
        let reach = g.reachable_from(&root);
        assert!(reach.contains(&a), "root reaches a directly");
        assert!(reach.contains(&b), "root reaches b transitively (multi-hop)");
        assert!(!reach.contains(&iso), "the isolated cell is unreachable");
        assert!(!reach.contains(&root), "a root does not list itself");
        assert_eq!(g.reach_count(&root), 2, "root's blast radius is {{a, b}}");
        // a reaches only b; b reaches nothing.
        assert_eq!(g.reach_count(&a), 1);
        assert_eq!(g.reach_count(&b), 0);
    }

    #[test]
    fn layered_layout_places_cells_at_their_delegation_depth() {
        // THE MULTI-HOP LAYOUT: root at depth 0, a at depth 1, b at depth 2.
        let (world, root, a, b, _iso) = chain_world();
        let g = OcapGraph::build(&world);
        let layers = g.layered_from(&root);
        assert_eq!(layers.len(), 3, "three delegation depths: root, a, b");
        assert_eq!(layers[0].cells, vec![root]);
        assert_eq!(layers[1].cells, vec![a]);
        assert_eq!(layers[2].cells, vec![b]);
    }

    #[test]
    fn source_roots_are_the_cells_with_no_inbound_edge() {
        let (world, root, _a, _b, iso) = chain_world();
        let g = OcapGraph::build(&world);
        let roots = g.source_roots();
        // root and iso have no inbound edge; a and b do.
        assert!(roots.contains(&root));
        assert!(roots.contains(&iso));
        assert_eq!(roots.len(), 2);
    }

    #[test]
    fn an_acyclic_delegation_chain_has_no_cycle() {
        // The real-executor chain root → a → b is acyclic — the detector agrees.
        let (world, root, a, _b, _iso) = chain_world();
        let g = OcapGraph::build(&world);
        assert!(!g.has_cycle_from(&root), "the chain root→a→b is acyclic");
        assert!(!g.has_cycle_from(&a), "the sub-chain a→b is acyclic");
    }

    #[test]
    fn a_mutual_delegation_cycle_is_detected() {
        // Mutual authority a ⇄ b is a legitimate cap-graph shape (each cell
        // holds a cap reaching the other). The cap ids are content-addressed and
        // caps are added after derivation, so two mutually-pointing cells are
        // most directly constructed by building the graph then asserting the
        // structural detector — the topology test the panel relies on to flag a
        // delegation loop. We build the graph from a real world and add the
        // closing edge the way a later grant turn would (b granted a cap to a).
        let mut world = World::new();
        let a = world.genesis_cell(0xA1, 1_000);
        // b is born holding a cap reaching a (b → a).
        let (b, _slot) = world.genesis_cell_with_cap(0xB1, 1_000, a);
        let mut g = OcapGraph::build(&world);
        // Acyclic so far (only b → a).
        assert!(!g.has_cycle_from(&b));
        // Close the loop: a → b (the edge a later turn would add once a holds a
        // cap to b — e.g. via an introduction). The detector must catch a ⇄ b.
        g.adjacency.entry(a).or_default().insert(b);
        assert!(g.has_cycle_from(&a), "a ⇄ b is a cycle");
        assert!(g.has_cycle_from(&b), "the cycle is reachable from b too");
    }

    #[test]
    fn a_self_loop_is_a_cycle() {
        // A self-referential authority x → x is the degenerate cycle.
        let mut g = OcapGraph::build(&World::new());
        let x = CellId::from_bytes([0x5Au8; 32]);
        g.adjacency.entry(x).or_default().insert(x);
        assert!(g.has_cycle_from(&x), "a self-loop x→x is a cycle");
    }
}
