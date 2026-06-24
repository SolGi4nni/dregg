//! THE MOLDABLE FACES — `present()` as a multiplicity of observations.
//!
//! Every cell exports up to seven faces (the `Presentable` framework); each is a
//! distinct `Obs`-projection of the same cell. This crate ports the faces that are
//! PURE functions of a `Cell` + `Ledger` + receipts (the gpui-free, substrate-only
//! subset):
//!
//!   - **RawFields** — the [`Inspectable`] four-substance field tree;
//!   - **Graph** — the cell's local ocap neighbourhood (edges in/out);
//!   - **DomainVisual** — the lifecycle state machine (Live/Sealed/…);
//!   - **Provenance** — the receipt-chain lineage (the turns this cell agented).
//!
//! The deep L2–L10 lenses (Invariant verifiers, Source/Datalog, gadget builders)
//! and the per-viewer Affordances face compose on top via [`crate::affordances`] +
//! [`crate::frustum`]; they are not emitted by the bare [`ReflectedCell`] here.

use dregg_cell::{Cell, Ledger};
use dregg_turn::turn::TurnReceipt;
use dregg_types::CellId;

use crate::graph::{GraphEdge, GraphNode, OcapGraph};
use crate::substance::{Inspectable, reflect_cell, short_hex};

/// Which of the seven moldable lenses a [`Presentation`] is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PresentationKind {
    /// The [`Inspectable`] field tree — the MANDATORY floor.
    RawFields,
    /// A node/edge view (the ocap neighbourhood).
    Graph,
    /// A domain rendering (the lifecycle state machine).
    DomainVisual,
    /// The receipt-chain / lineage face.
    Provenance,
}

impl PresentationKind {
    /// A short stable slug (a tab key / test selector).
    pub fn slug(&self) -> &'static str {
        match self {
            PresentationKind::RawFields => "raw-fields",
            PresentationKind::Graph => "graph",
            PresentationKind::DomainVisual => "domain-visual",
            PresentationKind::Provenance => "provenance",
        }
    }
}

/// One presentation: a kind + a renderable payload + searchable text.
#[derive(Clone, Debug)]
pub struct Presentation {
    pub kind: PresentationKind,
    /// Operator-legible label ("Cell State", "ocap Graph").
    pub label: String,
    /// The pure-data payload a thin view layer renders.
    pub body: PresentationBody,
    /// Flattened content a fuzzy search indexes.
    pub search_text: String,
}

/// The renderable payloads (each pure data).
#[derive(Clone, Debug)]
pub enum PresentationBody {
    /// REUSES the substance field tree — the RawFields floor.
    Fields(Inspectable),
    /// Nodes + typed edges (the ocap neighbourhood).
    Graph(GraphView),
    /// States + transitions + current (the lifecycle).
    StateMachine(StateMachineView),
    /// Ordered events (the receipt chain).
    Timeline(TimelineView),
}

/// A node/edge view centered on `focus`.
#[derive(Clone, Debug)]
pub struct GraphView {
    pub nodes: Vec<GraphNode>,
    pub edges: Vec<GraphEdge>,
    pub focus: Option<CellId>,
}

/// One state in a [`StateMachineView`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SmState {
    pub name: String,
    pub terminal: bool,
}

/// One directed transition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SmTransition {
    pub from: String,
    pub to: String,
    pub verb: String,
}

/// States + transitions + the current state.
#[derive(Clone, Debug)]
pub struct StateMachineView {
    pub states: Vec<SmState>,
    pub transitions: Vec<SmTransition>,
    pub current: String,
}

/// One event in a [`TimelineView`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TimelineEvent {
    /// A monotone ordering key (index / height).
    pub at: u64,
    pub label: String,
    /// An optional navigable hash (the receipt this event IS).
    pub hash: Option<[u8; 32]>,
}

/// Ordered events — a receipt chain / lineage.
#[derive(Clone, Debug)]
pub struct TimelineView {
    pub events: Vec<TimelineEvent>,
}

/// A reflected cell — the focus a [`Presentation`] set is built around (a snapshot of
/// the cell off the ledger).
pub struct ReflectedCell {
    pub id: CellId,
    pub cell: Cell,
}

impl ReflectedCell {
    /// Snapshot a cell off the ledger, if present.
    pub fn from_ledger(ledger: &Ledger, id: CellId) -> Option<Self> {
        ledger.get(&id).map(|c| ReflectedCell {
            id,
            cell: c.clone(),
        })
    }

    /// **The moldable multiplicity** — every face this cell presents, given the live
    /// `ledger` (for the ocap neighbourhood) and `receipts` (for the lineage).
    pub fn present(&self, ledger: &Ledger, receipts: &[TurnReceipt]) -> Vec<Presentation> {
        vec![
            self.raw_fields(),
            self.graph_face(ledger),
            self.domain_visual(),
            self.provenance(receipts),
        ]
    }

    /// RawFields — the four-substance field tree (the mandatory floor).
    pub fn raw_fields(&self) -> Presentation {
        let inspectable = reflect_cell(&self.id, &self.cell);
        let search_text = inspectable
            .fields
            .iter()
            .map(|f| f.key.as_str())
            .collect::<Vec<_>>()
            .join(" ");
        Presentation {
            kind: PresentationKind::RawFields,
            label: "Cell State".into(),
            body: PresentationBody::Fields(inspectable),
            search_text,
        }
    }

    /// Graph — the cell's local ocap neighbourhood (edges in/out + the touched nodes).
    pub fn graph_face(&self, ledger: &Ledger) -> Presentation {
        let g = OcapGraph::build(ledger);
        let mut keep: std::collections::BTreeSet<CellId> = std::collections::BTreeSet::new();
        keep.insert(self.id);
        let mut edges = Vec::new();
        for e in g.edges_from(&self.id) {
            keep.insert(e.target);
            edges.push(e.clone());
        }
        for e in g.edges_to(&self.id) {
            keep.insert(e.holder);
            edges.push(e.clone());
        }
        let nodes: Vec<GraphNode> = g
            .nodes()
            .iter()
            .filter(|n| keep.contains(&n.cell))
            .cloned()
            .collect();
        Presentation {
            kind: PresentationKind::Graph,
            label: "ocap Graph".into(),
            body: PresentationBody::Graph(GraphView {
                nodes,
                edges,
                focus: Some(self.id),
            }),
            search_text: format!("ocap graph {}", short_hex(self.id.as_bytes())),
        }
    }

    /// DomainVisual — the lifecycle state machine, with the current state highlighted.
    pub fn domain_visual(&self) -> Presentation {
        Presentation {
            kind: PresentationKind::DomainVisual,
            label: "Lifecycle".into(),
            body: PresentationBody::StateMachine(lifecycle_state_machine(&self.cell)),
            search_text: format!(
                "lifecycle {}",
                crate::substance::lifecycle_label(&self.cell)
            ),
        }
    }

    /// Provenance — the receipt-chain lineage: the turns THIS cell agented, in order.
    pub fn provenance(&self, receipts: &[TurnReceipt]) -> Presentation {
        let mut events = Vec::new();
        for (i, r) in receipts.iter().enumerate() {
            if r.agent == self.id {
                events.push(TimelineEvent {
                    at: i as u64,
                    label: format!(
                        "turn #{i} · {} actions · {} computrons",
                        r.action_count, r.computrons_used
                    ),
                    hash: Some(r.receipt_hash()),
                });
            }
        }
        Presentation {
            kind: PresentationKind::Provenance,
            label: "Provenance".into(),
            body: PresentationBody::Timeline(TimelineView { events }),
            search_text: format!("provenance {}", short_hex(self.id.as_bytes())),
        }
    }
}

/// The cell-lifecycle state machine (Live/Sealed/Destroyed/Migrated/Archived).
pub fn lifecycle_state_machine(cell: &Cell) -> StateMachineView {
    use dregg_cell::lifecycle::CellLifecycle;
    let states = vec![
        SmState {
            name: "Live".into(),
            terminal: false,
        },
        SmState {
            name: "Sealed".into(),
            terminal: false,
        },
        SmState {
            name: "Destroyed".into(),
            terminal: true,
        },
        SmState {
            name: "Migrated".into(),
            terminal: true,
        },
        SmState {
            name: "Archived".into(),
            terminal: false,
        },
    ];
    let transitions = vec![
        SmTransition {
            from: "Live".into(),
            to: "Sealed".into(),
            verb: "Seal".into(),
        },
        SmTransition {
            from: "Sealed".into(),
            to: "Live".into(),
            verb: "Unseal".into(),
        },
        SmTransition {
            from: "Live".into(),
            to: "Destroyed".into(),
            verb: "Destroy".into(),
        },
        SmTransition {
            from: "Live".into(),
            to: "Migrated".into(),
            verb: "Migrate".into(),
        },
        SmTransition {
            from: "Live".into(),
            to: "Archived".into(),
            verb: "Archive".into(),
        },
    ];
    let current = match cell.lifecycle {
        CellLifecycle::Live => "Live",
        CellLifecycle::Sealed { .. } => "Sealed",
        CellLifecycle::Destroyed { .. } => "Destroyed",
        CellLifecycle::Migrated { .. } => "Migrated",
        CellLifecycle::Archived { .. } => "Archived",
    }
    .to_string();
    StateMachineView {
        states,
        transitions,
        current,
    }
}
