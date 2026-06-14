//! THE COORDINATION GRAPH — the causal shape of the swarm (N17).
//!
//! A small directed view of how a swarm's members coordinate, built purely from
//! the live [`Swarm`] + [`World`] (gpui-free, `cargo test`-able). Two relations,
//! drawn as two layers (`docs/ADOS-DEEPENING.md` §3.4, `docs/AGENT-SWARM-UX.md`
//! §4.3):
//!
//!   * **NODES** are the swarm's members (one per member, in boot order).
//!   * **NOTIFY ARROWS** ([`NotifyArrow`]) are the deposited [`NotifyEdge`]s — the
//!     async wakes one member's committed `EmitEvent` turn deposited in another's
//!     inbox. A→B means "A woke B" (the sender → the inbox holder). These are the
//!     CAUSALITY of the swarm: the arrow lands on emit and fades on drain. They do
//!     NOT imply synchronization — the two receipts (sender's emit, recipient's
//!     drain) are independent (the ocap async-message model).
//!   * **MANDATE EDGES** ([`MandateArrow`]) are the FAINTER background reach graph:
//!     a directed edge `holder ──▶ target` for every capability a member holds
//!     reaching ANOTHER member (the real c-list, restricted to the swarm). This is
//!     "who CAN reach whom" — the structural authority the executor will enforce,
//!     drawn behind the live notify arrows.
//!
//! The whole point (the deepest legibility win over a log scroll): a flat feed
//! cannot show a DAG, and agent coordination *is* a DAG. The pale-ghost question
//! for the graph: *can the operator be fooled about who woke whom, or about who
//! CAN reach whom?* No — every notify arrow is a real deposited edge from a
//! committed turn, and every mandate edge is a real `CapabilityRef` read from the
//! live ledger (never a parallel model).
//!
//! # The layout
//!
//! [`SwarmGraph::build`] computes a DETERMINISTIC layout: members are placed on a
//! circle in boot order (the canonical swarm ordering), so the same swarm always
//! lays out identically (no force simulation, no RNG — a test can assert exact
//! positions). The cockpit renders the nodes at these positions and draws the two
//! arrow layers between them.
//!
//! # The single-image boundary
//!
//! This graph shows the members of THIS image's swarm (n=1). A cross-image swarm
//! (members on different federated nodes) is the federation-connect lane (the same
//! model over the peer view) — named, not faked.

use std::collections::BTreeSet;

use dregg_cell::CellId;

use crate::swarm::Swarm;
use crate::world::World;

/// One node in the coordination graph — a swarm member at a laid-out position.
#[derive(Clone, Debug, PartialEq)]
pub struct SwarmNode {
    /// The member cell this node IS.
    pub agent: CellId,
    /// A short operator-legible id (abbreviated cell id).
    pub short: String,
    /// The member's operator-assigned name.
    pub name: String,
    /// The member's index in boot order (its stable ordinal — the layout seed).
    pub index: usize,
    /// The deterministic layout position (x, y) in a unit-ish coordinate space
    /// (a circle of radius ~1 centered at the origin; the panel scales it).
    pub x: f32,
    pub y: f32,
    /// Whether the backing cell is live in the ledger (a dead member reads
    /// honestly — drawn faded).
    pub backed: bool,
    /// How many pending (undrained) notify arrows point AT this node (its inbox
    /// PENDING badge count).
    pub pending_in: usize,
}

/// One NOTIFY ARROW — a deposited async wake from `from` to `to` (the sender's
/// committed `EmitEvent` deposited a [`NotifyEdge`] in `to`'s inbox). The live
/// causality layer: "from woke to".
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotifyArrow {
    /// The member whose committed turn deposited the wake (the sender / tail).
    pub from: CellId,
    /// The member whose inbox holds the wake (the recipient / head).
    pub to: CellId,
    /// The topic hash of the wake (Blake3 of the topic string).
    pub topic_hash: [u8; 32],
    /// Whether this wake has been DRAINED (the arrow fades) or is still PENDING
    /// (the arrow is live).
    pub drained: bool,
    /// The sender's receipt hash (the provenance link the edge carries).
    pub sender_receipt: [u8; 32],
}

impl NotifyArrow {
    /// Whether the arrow is live (a pending, undrained wake).
    pub fn is_pending(&self) -> bool {
        !self.drained
    }

    /// A short operator-legible label for the arrow.
    pub fn label(&self) -> String {
        format!(
            "{} → {} topic 0x{}{}",
            crate::reflect::short_hex(self.from.as_bytes()),
            crate::reflect::short_hex(self.to.as_bytes()),
            hex::encode(&self.topic_hash[..4]),
            if self.drained { " (drained)" } else { " (pending)" },
        )
    }
}

/// One MANDATE EDGE — a capability `holder` holds reaching `target`, BOTH being
/// swarm members (the fainter background reach graph: who CAN reach whom). The
/// structural authority the executor enforces, drawn behind the notify arrows.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MandateArrow {
    /// The member holding the capability (the grantor / tail).
    pub holder: CellId,
    /// The member the capability reaches (the head).
    pub target: CellId,
}

/// THE COORDINATION GRAPH — the swarm's members as nodes, their async notify
/// wakes as the live arrows, their inter-member capabilities as the background
/// reach graph, in a deterministic layout. Built from the live [`Swarm`] +
/// [`World`]; gpui-free.
#[derive(Clone, Debug)]
pub struct SwarmGraph {
    /// The member nodes (boot order, each at its deterministic position).
    pub nodes: Vec<SwarmNode>,
    /// The notify arrows (the deposited wakes — the causality layer).
    pub notify_arrows: Vec<NotifyArrow>,
    /// The mandate edges (inter-member capabilities — the background reach graph).
    pub mandate_edges: Vec<MandateArrow>,
}

impl SwarmGraph {
    /// **Build the coordination graph** from the live swarm + world:
    ///   * nodes = the members, laid out on a deterministic circle (boot order);
    ///   * notify arrows = every [`NotifyEdge`] in every member's inbox, as an
    ///     arrow `edge.from → (the inbox-holding member)`;
    ///   * mandate edges = every capability a member holds reaching ANOTHER member
    ///     (the inter-member slice of the real cap-graph, read from the ledger).
    pub fn build(swarm: &Swarm, world: &World) -> Self {
        let members = swarm.members();
        let n = members.len();

        // The set of member ids (to restrict the mandate reach graph to the swarm).
        let member_set: BTreeSet<CellId> = members.iter().map(|m| m.agent).collect();

        // NODES — deterministic circular layout in boot order. Member i sits at
        // angle 2πi/n (starting at the top, going clockwise), radius 1. With one
        // member it sits at the origin's top; the layout is fully determined by
        // the boot order, so a test can assert exact positions.
        let nodes: Vec<SwarmNode> = members
            .iter()
            .enumerate()
            .map(|(i, m)| {
                let (x, y) = circle_position(i, n);
                SwarmNode {
                    agent: m.agent,
                    short: m.short.clone(),
                    name: m.name.clone(),
                    index: i,
                    x,
                    y,
                    backed: m.backed,
                    pending_in: m.pending_notify_count(),
                }
            })
            .collect();

        // NOTIFY ARROWS — one per NotifyEdge in each member's inbox. The inbox
        // holder is the recipient (`to`); the edge's `from` is the sender. We emit
        // arrows for both pending and drained edges (the panel fades the drained).
        let mut notify_arrows: Vec<NotifyArrow> = Vec::new();
        for m in members {
            for edge in &m.inbox {
                notify_arrows.push(NotifyArrow {
                    from: edge.from,
                    to: m.agent,
                    topic_hash: edge.topic_hash,
                    drained: edge.drained,
                    sender_receipt: edge.sender_receipt,
                });
            }
        }

        // MANDATE EDGES — the inter-member reach graph from the live c-lists. For
        // each member, every capability it holds whose target is ANOTHER member is
        // an edge `holder → target`. De-duplicated (a member may hold the same
        // target at several slots; the reach graph has one edge per (holder,
        // target) pair). Read straight from the ledger — the real cap-graph.
        let mut seen: BTreeSet<(CellId, CellId)> = BTreeSet::new();
        let mut mandate_edges: Vec<MandateArrow> = Vec::new();
        for m in members {
            if let Some(cell) = world.ledger().get(&m.agent) {
                for cap in cell.capabilities.iter() {
                    if cap.target != m.agent
                        && member_set.contains(&cap.target)
                        && seen.insert((m.agent, cap.target))
                    {
                        mandate_edges.push(MandateArrow {
                            holder: m.agent,
                            target: cap.target,
                        });
                    }
                }
            }
        }

        SwarmGraph {
            nodes,
            notify_arrows,
            mandate_edges,
        }
    }

    /// The number of member nodes.
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// The live (pending) notify arrows — the wakes not yet drained.
    pub fn pending_arrows(&self) -> Vec<&NotifyArrow> {
        self.notify_arrows.iter().filter(|a| a.is_pending()).collect()
    }

    /// Whether `holder` CAN reach `target` in the mandate background (a direct
    /// inter-member capability) — the structural authority answer.
    pub fn can_reach(&self, holder: &CellId, target: &CellId) -> bool {
        self.mandate_edges
            .iter()
            .any(|e| &e.holder == holder && &e.target == target)
    }

    /// Look up a node by member id.
    pub fn node(&self, agent: &CellId) -> Option<&SwarmNode> {
        self.nodes.iter().find(|n| &n.agent == agent)
    }
}

/// The deterministic circular layout position of member `i` of `n`. Member 0 is
/// at the top (angle −π/2), going clockwise. A single member sits at the top of
/// the unit circle (0, -1); zero members is unreachable (callers pass `i < n`).
/// Fully determined by `(i, n)` — no RNG, no force simulation.
fn circle_position(i: usize, n: usize) -> (f32, f32) {
    if n <= 1 {
        // One member: the top of the circle (a stable, deterministic spot).
        return (0.0, -1.0);
    }
    let frac = i as f32 / n as f32;
    let angle = -std::f32::consts::FRAC_PI_2 + frac * std::f32::consts::TAU;
    (angle.cos(), angle.sin())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::swarm::Swarm;
    use crate::world::{emit_event, make_open_cell, transfer, World};

    /// A three-member swarm: coordinator (caps to BOTH workers), worker-a,
    /// worker-b — the same mandate graph the swarm tests use.
    fn swarm_world() -> (World, Swarm, CellId, CellId, CellId) {
        let mut world = World::new();
        let worker_a = world.genesis_cell(0xA0, 5_000);
        let worker_b = world.genesis_cell(0xB0, 5_000);
        let mut coord_cell = make_open_cell(0xC0, 10_000);
        coord_cell
            .capabilities
            .grant(worker_a, dregg_cell::AuthRequired::None)
            .expect("free slot");
        coord_cell
            .capabilities
            .grant(worker_b, dregg_cell::AuthRequired::None)
            .expect("free slot");
        let coord = world.genesis_install(coord_cell);
        let swarm = Swarm::new(
            &world,
            [(coord, "coordinator"), (worker_a, "worker-a"), (worker_b, "worker-b")],
        );
        (world, swarm, coord, worker_a, worker_b)
    }

    #[test]
    fn the_graph_has_a_node_per_member_in_boot_order() {
        let (world, swarm, coord, worker_a, worker_b) = swarm_world();
        let g = SwarmGraph::build(&swarm, &world);
        assert_eq!(g.node_count(), 3);
        // Boot order is preserved.
        assert_eq!(g.nodes[0].agent, coord);
        assert_eq!(g.nodes[1].agent, worker_a);
        assert_eq!(g.nodes[2].agent, worker_b);
        assert_eq!(g.nodes[0].index, 0);
        assert_eq!(g.nodes[0].name, "coordinator");
    }

    #[test]
    fn the_layout_is_deterministic() {
        // The SAME swarm lays out IDENTICALLY every build (no RNG, no force sim) —
        // member 0 at the top of the circle, the rest evenly spaced clockwise.
        let (world, swarm, _c, _wa, _wb) = swarm_world();
        let g1 = SwarmGraph::build(&swarm, &world);
        let g2 = SwarmGraph::build(&swarm, &world);
        for (a, b) in g1.nodes.iter().zip(g2.nodes.iter()) {
            assert_eq!((a.x, a.y), (b.x, b.y), "the layout is deterministic");
        }
        // Member 0 is at the top of the circle (0, -1).
        assert!((g1.nodes[0].x - 0.0).abs() < 1e-5);
        assert!((g1.nodes[0].y - (-1.0)).abs() < 1e-5);
        // Three members are evenly spaced — distinct positions.
        assert_ne!((g1.nodes[0].x, g1.nodes[0].y), (g1.nodes[1].x, g1.nodes[1].y));
        assert_ne!((g1.nodes[1].x, g1.nodes[1].y), (g1.nodes[2].x, g1.nodes[2].y));
    }

    #[test]
    fn the_mandate_background_matches_the_cap_graph() {
        // THE MANDATE EDGES: the background reach graph is exactly the inter-member
        // capabilities the cap-graph holds — coordinator → worker-a and
        // coordinator → worker-b, and nothing else (the workers hold no outbound
        // caps to peers).
        let (world, swarm, coord, worker_a, worker_b) = swarm_world();
        let g = SwarmGraph::build(&swarm, &world);
        assert_eq!(g.mandate_edges.len(), 2, "coordinator reaches both workers");
        assert!(g.can_reach(&coord, &worker_a), "coordinator → worker-a");
        assert!(g.can_reach(&coord, &worker_b), "coordinator → worker-b");
        // The workers hold no inter-member cap (they cannot reach peers).
        assert!(!g.can_reach(&worker_a, &worker_b));
        assert!(!g.can_reach(&worker_a, &coord));
        assert!(!g.can_reach(&worker_b, &coord));
        // The mandate edges are the real cap-graph: each edge's holder really holds
        // a cap to its target in the live ledger.
        for e in &g.mandate_edges {
            assert!(
                world.ledger().get(&e.holder).unwrap().capabilities.has_access(&e.target),
                "every mandate edge is a real held capability"
            );
        }
    }

    #[test]
    fn the_notify_arrows_match_the_deposited_notify_edges() {
        // THE NOTIFY ARROWS: after the coordinator emits to worker-a and worker-b,
        // the graph's arrows match the deposited NotifyEdges exactly — one
        // coordinator→worker-a, one coordinator→worker-b, both pending.
        let (mut world, mut swarm, coord, worker_a, worker_b) = swarm_world();
        swarm
            .run(&mut world, coord, vec![emit_event(worker_a, "task/a", vec![])])
            .expect("emit to worker-a");
        swarm
            .run(&mut world, coord, vec![emit_event(worker_b, "task/b", vec![])])
            .expect("emit to worker-b");

        let g = SwarmGraph::build(&swarm, &world);
        // Two notify arrows, both from the coordinator, both pending.
        assert_eq!(g.notify_arrows.len(), 2);
        assert_eq!(g.pending_arrows().len(), 2);
        assert!(
            g.notify_arrows.iter().any(|a| a.from == coord && a.to == worker_a && !a.drained),
            "an arrow coordinator → worker-a"
        );
        assert!(
            g.notify_arrows.iter().any(|a| a.from == coord && a.to == worker_b && !a.drained),
            "an arrow coordinator → worker-b"
        );
        // The arrows match the deposited edges: every arrow's (from, to,
        // topic, receipt) equals a NotifyEdge in the recipient's inbox.
        for arrow in &g.notify_arrows {
            let recipient = swarm.members().iter().find(|m| m.agent == arrow.to).unwrap();
            assert!(
                recipient.inbox.iter().any(|e| e.from == arrow.from
                    && e.topic_hash == arrow.topic_hash
                    && e.sender_receipt == arrow.sender_receipt
                    && e.drained == arrow.drained),
                "every arrow corresponds to a deposited NotifyEdge"
            );
        }
        // worker-a and worker-b each show one pending inbound wake.
        assert_eq!(g.node(&worker_a).unwrap().pending_in, 1);
        assert_eq!(g.node(&worker_b).unwrap().pending_in, 1);
        assert_eq!(g.node(&coord).unwrap().pending_in, 0);
    }

    #[test]
    fn a_drained_notify_arrow_fades_but_remains() {
        // When a wake is DRAINED, its arrow remains in the graph (the causality
        // history) but is marked drained (the panel fades it) and is no longer
        // pending.
        let (mut world, mut swarm, coord, worker_a, _wb) = swarm_world();
        swarm
            .run(&mut world, coord, vec![emit_event(worker_a, "task/a", vec![])])
            .expect("emit");
        swarm.drain_notify(&mut world, worker_a).expect("drain");

        let g = SwarmGraph::build(&swarm, &world);
        assert_eq!(g.notify_arrows.len(), 1, "the arrow remains in the history");
        assert!(g.notify_arrows[0].drained, "the arrow is marked drained");
        assert_eq!(g.pending_arrows().len(), 0, "no pending arrows after the drain");
        assert_eq!(g.node(&worker_a).unwrap().pending_in, 0, "the pending badge cleared");
    }

    #[test]
    fn an_empty_swarm_has_an_empty_graph() {
        let world = World::new();
        let swarm = Swarm::new(&world, Vec::<(CellId, String)>::new());
        let g = SwarmGraph::build(&swarm, &world);
        assert_eq!(g.node_count(), 0);
        assert!(g.notify_arrows.is_empty());
        assert!(g.mandate_edges.is_empty());
    }

    #[test]
    fn the_mandate_edges_exclude_non_member_targets() {
        // A member holding a cap to a cell OUTSIDE the swarm contributes NO mandate
        // edge (the background reach graph is the inter-MEMBER slice only).
        let mut world = World::new();
        let outsider = world.genesis_cell(0xDD, 0);
        // The coordinator holds a cap to an outsider (not a swarm member).
        let (coord, _slot) = world.genesis_cell_with_cap(0xC0, 1_000, outsider);
        let swarm = Swarm::new(&world, [(coord, "coordinator")]);
        let g = SwarmGraph::build(&swarm, &world);
        assert_eq!(g.node_count(), 1);
        assert!(
            g.mandate_edges.is_empty(),
            "a cap to a non-member is not an inter-member mandate edge"
        );
    }
}
