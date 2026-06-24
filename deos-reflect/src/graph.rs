//! THE OCAP GRAPH — the whole-image capability layout, built from a live
//! [`dregg_cell::Ledger`].
//!
//! Nodes are cells; edges are capability grants (`holder ──▶ target`, the literal
//! ocap primitive). It computes the multi-hop reachability closure (the blast radius
//! of a cell's authority — the topology that bounds which cells a viewer's frustum can
//! crawl) and a layered delegation-depth layout. Ported verbatim (algorithmically)
//! from starbridge-v2's gpui-free `graph.rs`, rebased off the cockpit `World` onto
//! `Ledger`.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use dregg_cell::{AuthRequired, Ledger};
use dregg_types::CellId;

use crate::substance::short_hex;

/// One node in the ocap graph — a cell, carrying the live state a node-link view
/// renders without a second ledger read.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GraphNode {
    pub cell: CellId,
    /// A short operator-legible id (abbreviated cell id).
    pub short: String,
    /// The cell's live balance (issuer wells carry −supply — render distinctly).
    pub balance: i64,
    /// The cell's lifecycle label.
    pub lifecycle: String,
    /// OUTBOUND capability edges (the breadth of authority it can hand on).
    pub out_degree: usize,
    /// INBOUND capability edges (how many holders can reach it).
    pub in_degree: usize,
}

/// One directed edge — a capability grant `holder ──▶ target` at `rights`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GraphEdge {
    /// The cell HOLDING the capability (the arrow's tail).
    pub holder: CellId,
    /// The cell the capability REACHES (the arrow's head).
    pub target: CellId,
    /// The holder's local c-list slot for this cap.
    pub slot: u32,
    /// The rights the holder wields over the target (the `AuthRequired` lattice).
    pub rights: AuthRequired,
    /// Whether the cap is confined to a subset of effect types (a facet).
    pub faceted: bool,
    /// An optional expiry height, if any.
    pub expires_at: Option<u64>,
    /// `Some(e)` marks a DELEGATED authority (stored from a grantor at epoch `e`);
    /// `None` is a DIRECT (self-origin) grant.
    pub delegated_epoch: Option<u64>,
}

impl GraphEdge {
    /// A short operator-legible label for the rights.
    pub fn rights_label(&self) -> &'static str {
        rights_label(&self.rights)
    }
    /// Whether this edge is a DELEGATED authority (carries a stored epoch).
    pub fn is_delegated(&self) -> bool {
        self.delegated_epoch.is_some()
    }
}

/// THE OCAP GRAPH — nodes = cells, edges = capability grants.
#[derive(Clone, Debug)]
pub struct OcapGraph {
    nodes: Vec<GraphNode>,
    edges: Vec<GraphEdge>,
    adjacency: BTreeMap<CellId, BTreeSet<CellId>>,
}

impl OcapGraph {
    /// Build the whole ocap graph from a live ledger: one node per cell, one edge per
    /// capability in every cell's c-list. Deterministic (id-sorted).
    pub fn build(ledger: &Ledger) -> Self {
        let mut edges: Vec<GraphEdge> = Vec::new();
        let mut adjacency: BTreeMap<CellId, BTreeSet<CellId>> = BTreeMap::new();
        let mut out_degree: BTreeMap<CellId, usize> = BTreeMap::new();
        let mut in_degree: BTreeMap<CellId, usize> = BTreeMap::new();

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

        let nodes: Vec<GraphNode> = cells
            .iter()
            .map(|(id, cell)| GraphNode {
                cell: **id,
                short: short_hex(id.as_bytes()),
                balance: cell.state.balance(),
                lifecycle: crate::substance::lifecycle_label(cell),
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
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }
    pub fn edge_count(&self) -> usize {
        self.edges.len()
    }
    /// The edges held BY `holder` (its outbound authority).
    pub fn edges_from(&self, holder: &CellId) -> Vec<&GraphEdge> {
        self.edges.iter().filter(|e| &e.holder == holder).collect()
    }
    /// The edges pointing AT `target` (who can reach it).
    pub fn edges_to(&self, target: &CellId) -> Vec<&GraphEdge> {
        self.edges.iter().filter(|e| &e.target == target).collect()
    }

    /// **THE MULTI-HOP REACHABILITY** — every cell `root` can reach transitively
    /// through the capability edges (the BFS closure: the blast radius of authority).
    /// `root` itself is NOT included. This is graph *topology* (who-points-to-whom);
    /// the executor's no-amplification gate still bounds the *rights* per hop.
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
                    if t != root && seen.insert(*t) {
                        queue.push_back(*t);
                    }
                }
            }
        }
        seen
    }

    /// The size of the multi-hop reach from `root`.
    pub fn reach_count(&self, root: &CellId) -> usize {
        self.reachable_from(root).len()
    }

    /// **THE LAYERED MULTI-HOP LAYOUT** from `root`: a BFS partition into delegation-
    /// DEPTH layers (root at 0, direct grantees at 1, …). Each layer id-sorted; a cell
    /// appears in its shortest depth; unreachable cells are omitted.
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
        let max_depth = depth.values().copied().max().unwrap_or(0);
        let mut layers: Vec<GraphLayer> = (0..=max_depth)
            .map(|d| GraphLayer {
                depth: d,
                cells: Vec::new(),
            })
            .collect();
        // `depth` is a BTreeMap keyed by CellId, so iterating it yields cells in
        // ascending id order; each per-depth bucket is therefore already id-sorted
        // (the previous per-layer re-sort was redundant).
        let mut by_depth: Vec<Vec<CellId>> = vec![Vec::new(); max_depth + 1];
        for (cell, d) in &depth {
            by_depth[*d].push(*cell);
        }
        for (d, cells) in by_depth.into_iter().enumerate() {
            layers[d].cells = cells;
        }
        layers
    }

    /// Whether the graph has a directed cycle reachable from `root` (mutual /
    /// circular delegation). Not a bug — but revocation reasoning must account for it.
    pub fn has_cycle_from(&self, root: &CellId) -> bool {
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
                        1 => return true,
                        2 => {}
                        _ => stack.push((*t, false)),
                    }
                }
            }
        }
        false
    }

    /// The roots: cells with NO inbound edge (the authority sources).
    pub fn source_roots(&self) -> Vec<CellId> {
        let targeted: std::collections::HashSet<CellId> =
            self.edges.iter().map(|e| e.target).collect();
        self.nodes
            .iter()
            .map(|n| n.cell)
            .filter(|c| !targeted.contains(c))
            .collect()
    }
}

/// One delegation-depth layer of the layered layout.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GraphLayer {
    pub depth: usize,
    pub cells: Vec<CellId>,
}

/// A short operator-legible label for an `AuthRequired` rights value.
pub fn rights_label(rights: &AuthRequired) -> &'static str {
    match rights {
        AuthRequired::None => "open",
        AuthRequired::Signature => "sig",
        AuthRequired::Either => "either",
        AuthRequired::Impossible => "impossible",
        _ => "proof",
    }
}
