//! **THE GRAPH CARD** — the cockpit's GRAPH surface (the ocap web), reborn as a deos-js
//! card.
//!
//! Today the cockpit's graph surface is hardcoded Rust gpui: its UI is *compiled code*.
//! This module makes it a **deos-js card** — a cell whose view is a *view-tree*
//! ([`crate::card_editor::ViewTree`], the same `{kind, props, children}` shape
//! [`deos-view`] renders) generated from the live World's CAPABILITY web (the ocap graph):
//!
//!   - the **edges section** — one row per capability edge `holder ──▶ target @rights`
//!     (a labeled [`ViewTree::Text`]), the literal ocap primitive (who-can-reach-what),
//!     read off the live ledger via [`deos_reflect::OcapGraph`]. This is the textual/list
//!     view of the cap-edges between cells.
//!   - the **nodes section** — one row per cell (short id + out/in degree), the breadth of
//!     each cell's authority and how many holders can reach it.
//!
//! Because the view is *data* (a view-tree = the card's `view_source` document), it is
//! **editable from within**: [`GraphCard::edit_view`] patches the graph card's OWN
//! view-source as a *receipted patch* with *blame*, landing a real provenance receipt on the
//! card's OWN cell's chain (the same [`Applet`]-backed authorship turn the inspector card
//! uses). The reshape is an accountable patch, not a recompile.
//!
//! ## The live World
//!
//! The graph card reflects over a PROVIDED ledger — the data is the live cap web, never a
//! parallel copy. The card itself is one sovereign cell (its own [`Applet`]), so an
//! edit-from-within receipts on its chain.
//!
//! ## The cap tooth is kept
//!
//! A view-edit is admitted only when `held` satisfies the card's `edit_authority`
//! ([`GraphCard::authorized`], the proven [`dregg_cell::is_attenuation`] gate). An
//! unauthorized reshape is refused in-band — no patch, no receipt.

use dregg_cell::{AuthRequired, Ledger};
use dregg_doc::{Author, BlameLine};
use dregg_turn::TurnReceipt;
use dregg_types::CellId;

use deos_reflect::substance::short_hex;
use deos_reflect::OcapGraph;

use crate::applet::{pack_u64, Affordance, Applet, Slot};
use crate::card_editor::{
    ButtonProps, EditError, OnClick, TextProps, ViewEdit, ViewPatch, ViewTree,
};
use crate::program_doc::ProgramSource;
use dregg_cell::{Credential, Requirement};

/// The heap slot the graph card bumps to leave a provenance receipt for a *structural*
/// authoring gesture. Disjoint from the inspector + objects card authorship slots so a
/// cockpit hosting all three does not collide.
pub const GRAPH_AUTHORSHIP_SLOT: Slot = 17;

/// One cap edge as the card reads it back: `holder ──▶ target @rights` — the literal ocap
/// primitive (who-can-reach-what), the row the edges section renders.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct GraphRow {
    /// The cell HOLDING the capability (the arrow's tail).
    pub holder: CellId,
    /// The cell the capability REACHES (the arrow's head).
    pub target: CellId,
    /// The holder's short id.
    pub holder_short: String,
    /// The target's short id.
    pub target_short: String,
    /// The rights the holder wields over the target (a short label).
    pub rights: String,
    /// Whether the cap is DELEGATED (carries a stored grantor epoch).
    pub delegated: bool,
}

/// **The graph card** — a deos-js card whose view is a view-tree generated from the live
/// World's ocap web (a row per cap-edge `holder ──▶ target @rights` + a node section),
/// reflected over a provided ledger, and editable from within (each reshape a receipted
/// patch).
pub struct GraphCard {
    /// The card's OWN sovereign cell — the substance an edit-from-within receipts against.
    /// NOT one of the cells the graph relates.
    card: Applet,
    /// The graph card's view-source AS A DOCUMENT (a patch-history).
    view: ProgramSource,
    /// The authority the card's driver holds — the cap a view-edit is checked against.
    held: AuthRequired,
    /// The authority a view-edit on THIS card requires (the authoring cap tooth).
    edit_authority: Requirement,
    /// The author every view-patch is attributed to (the blame identity).
    author: Author,
}

impl GraphCard {
    /// **Open a graph card** over a live World (`ledger`), authored by `author`. `held` is
    /// the driver's authority and `edit_authority` the cap a view-reshape requires. The
    /// initial view-tree is GENERATED from the ledger's ocap web and seeded as the card's
    /// editable `view_source` document. The card mints its OWN cell from `card_pk`.
    pub fn open(
        ledger: &Ledger,
        card_pk: [u8; 32],
        author: Author,
        held: AuthRequired,
        edit_authority: Requirement,
    ) -> Self {
        let card = Applet::mint(card_pk, [0u8; 32], &[], Vec::new(), held.clone());
        let initial = graph_view_for(ledger).to_json();
        let view = ProgramSource::seed(author, &initial);
        GraphCard {
            card,
            view,
            held,
            edit_authority,
            author,
        }
    }

    /// The card's OWN cell (read-only) — its model, its receipts, its chain.
    pub fn card(&self) -> &Applet {
        &self.card
    }

    /// The graph card's current view source (the document fold).
    pub fn view_source(&self) -> String {
        self.view.view_source()
    }

    /// The graph card's view-tree (the re-folded shape a renderer paints).
    pub fn view_tree(&self) -> Result<ViewTree, EditError> {
        ViewTree::from_json(&self.view.view_source()).map_err(EditError::BadView)
    }

    /// The blame over the graph card's view source — who authored each view line.
    pub fn view_blame(&self) -> Vec<BlameLine> {
        self.view.blame()
    }

    /// **The cap-edge rows** off a live ledger: one [`GraphRow`] per capability grant. The
    /// view's DATA (a pure function of the live ocap web).
    pub fn edges(&self, ledger: &Ledger) -> Vec<GraphRow> {
        graph_rows(ledger)
    }

    /// **The multi-hop reach** of `root` (the blast radius of its authority) off `ledger` —
    /// the BFS closure through the cap edges. Useful for the cockpit's "what can this cell
    /// reach" affordance.
    pub fn reach_of(&self, ledger: &Ledger, root: &CellId) -> Vec<CellId> {
        OcapGraph::build(ledger)
            .reachable_from(root)
            .into_iter()
            .collect()
    }

    /// **Regenerate** the view-tree from the live ledger's *current* ocap web, replacing the
    /// view-source as a fresh patch (used when the World advances — a grant/revoke changes
    /// the cap web). The from-within edits in [`Self::edit_view`] reshape on top.
    pub fn regenerate_view(&mut self, ledger: &Ledger) {
        let fresh = graph_view_for(ledger).to_json();
        self.view.edit(self.author, &fresh);
    }

    /// Whether the card is authorized to reshape its own view (the authoring cap tooth).
    fn authorized(&self) -> bool {
        self.edit_authority.satisfied_by(&self.held)
    }

    /// Fire a real `SetField` provenance turn bumping the card's authorship slot — how a
    /// *structural* reshape lands a receipt on the card's chain.
    fn provenance_turn(&mut self) -> Result<TurnReceipt, EditError> {
        let next = self.card.model().field_u64(GRAPH_AUTHORSHIP_SLOT) + 1;
        self.card.register_affordance(Affordance {
            name: "__graph_authorship__".into(),
            required: self.edit_authority.clone(),
            apply: Box::new(move |_model, _arg| vec![(GRAPH_AUTHORSHIP_SLOT, pack_u64(next))]),
        });
        self.card
            .fire("__graph_authorship__", 0)
            .map_err(|e| EditError::Fire(e.to_string()))
    }

    /// **EDIT THE VIEW FROM WITHIN — the keystone.** Apply a structural reshape (relabel a
    /// section, add a button, append a note) to the graph card's OWN view-tree, append the
    /// result as a PATCH to the card's `view_source` document, and leave a provenance
    /// receipt on the card's chain. Refused in-band if `held` does not satisfy
    /// `edit_authority`, or if the reshape changed nothing.
    pub fn edit_view(&mut self, patch: ViewPatch) -> Result<ViewEdit, EditError> {
        if !self.authorized() {
            return Err(EditError::Unauthorized);
        }
        let mut tree = self.view_tree()?;
        if !apply_view_patch(&patch, &mut tree) {
            return Err(EditError::NoOp);
        }
        let new_source = tree.to_json();
        self.view.edit(self.author, &new_source);
        let receipt = self.provenance_turn()?;
        let tree = self.view_tree()?;
        Ok(ViewEdit {
            tree,
            blame: self.view.blame(),
            receipt,
        })
    }
}

// ── view-tree generation (the graph card's view IS the live ocap web's data) ────────────

/// **Generate the graph view-tree** from a live ledger: a titled column with an edges
/// section (a row per cap-edge `holder ──▶ target @rights`) + a nodes section (a row per
/// cell with its out/in degree).
fn graph_view_for(ledger: &Ledger) -> ViewTree {
    let g = OcapGraph::build(ledger);
    let rows = rows_of(&g);

    let mut top: Vec<ViewTree> = Vec::new();
    top.push(text(&format!(
        "Ocap web · {} cells · {} edges",
        g.node_count(),
        g.edge_count()
    )));

    // ── Edges section: who-can-reach-what ──────────────────────────────────────────
    let mut edges: Vec<ViewTree> = vec![text("Cap edges (holder → target)")];
    if rows.is_empty() {
        edges.push(text("(no cap edges)"));
    } else {
        for r in &rows {
            let deleg = if r.delegated { " (delegated)" } else { "" };
            edges.push(text(&format!(
                "{} → {} @{}{}",
                r.holder_short, r.target_short, r.rights, deleg
            )));
        }
    }
    top.push(ViewTree::VStack { children: edges });

    // ── Nodes section: each cell's authority breadth ────────────────────────────────
    let mut nodes: Vec<ViewTree> = vec![text("Cells (out/in degree)")];
    for n in g.nodes() {
        nodes.push(ViewTree::Row {
            children: vec![
                text(&format!(
                    "{} · out {} / in {}",
                    n.short, n.out_degree, n.in_degree
                )),
                button(
                    "reach",
                    &format!("reach:{}", short_hex(n.cell.as_bytes())),
                    1,
                ),
            ],
        });
    }
    top.push(ViewTree::VStack { children: nodes });

    ViewTree::VStack { children: top }
}

/// **Generate the graph view-tree (the public entry).** A renderer (`deos-view`) parses
/// the JSON of this and paints it over the graph card; the per-cell `reach` buttons map to
/// the cockpit's "what can this cell reach" affordance, the edge rows to the live cap web.
pub fn graph_view(ledger: &Ledger) -> ViewTree {
    graph_view_for(ledger)
}

/// **The cap-edge rows** off a live ledger: one per capability grant, holder-then-target
/// ordered (deterministic).
pub fn graph_rows(ledger: &Ledger) -> Vec<GraphRow> {
    rows_of(&OcapGraph::build(ledger))
}

fn rows_of(g: &OcapGraph) -> Vec<GraphRow> {
    let mut rows: Vec<GraphRow> = g
        .edges()
        .iter()
        .map(|e| GraphRow {
            holder: e.holder,
            target: e.target,
            holder_short: short_hex(e.holder.as_bytes()),
            target_short: short_hex(e.target.as_bytes()),
            rights: e.rights_label().to_string(),
            delegated: e.is_delegated(),
        })
        .collect();
    rows.sort_by(|a, b| {
        a.holder
            .as_bytes()
            .cmp(b.holder.as_bytes())
            .then(a.target.as_bytes().cmp(b.target.as_bytes()))
    });
    rows
}

fn text(s: &str) -> ViewTree {
    ViewTree::Text {
        props: TextProps {
            text: s.to_string(),
        },
    }
}

fn button(label: &str, turn: &str, arg: i64) -> ViewTree {
    ViewTree::Button {
        props: ButtonProps {
            label: label.to_string(),
            on_click: OnClick {
                turn: turn.to_string(),
                arg,
            },
        },
    }
}

// ── the view-patch reshape (mirrors the inspector card's) ───────────────────────────────

fn apply_view_patch(patch: &ViewPatch, tree: &mut ViewTree) -> bool {
    match patch {
        ViewPatch::AddButton { label, turn, arg } => push_child(tree, button(label, turn, *arg)),
        ViewPatch::AddText { text: t } => push_child(tree, text(t)),
        ViewPatch::AddBind { slot, label } => push_child(
            tree,
            ViewTree::Bind {
                props: crate::card_editor::BindProps {
                    slot: *slot,
                    label: label.clone(),
                },
            },
        ),
        ViewPatch::Relabel { from, to } => relabel_text(tree, from, to),
    }
}

fn push_child(tree: &mut ViewTree, node: ViewTree) -> bool {
    match tree {
        ViewTree::VStack { children } | ViewTree::Row { children } => {
            children.push(node);
            true
        }
        _ => false,
    }
}

fn relabel_text(tree: &mut ViewTree, from: &str, to: &str) -> bool {
    if let ViewTree::Text { props } = tree {
        if props.text == from {
            props.text = to.to_string();
            return true;
        }
    }
    match tree {
        ViewTree::VStack { children } | ViewTree::Row { children } => {
            for c in children.iter_mut() {
                if relabel_text(c, from, to) {
                    return true;
                }
            }
            false
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::Cell;

    /// A small World with a real cap edge: cell A grants a Signature-rights capability to
    /// cell B, so the ocap web has one edge `A ──▶ B @sig`. The graph card reflects over it.
    fn world_with_edge() -> (Ledger, CellId, CellId) {
        let mut ledger = Ledger::new();
        let mut a = Cell::with_balance([0xA1; 32], [0u8; 32], 1_000);
        let b = Cell::with_balance([0xB2; 32], [0u8; 32], 500);
        let a_id = a.id();
        let b_id = b.id();
        a.capabilities.grant(b_id, AuthRequired::Signature);
        ledger.insert_cell(a).expect("insert A");
        ledger.insert_cell(b).expect("insert B");
        (ledger, a_id, b_id)
    }

    fn graph_card_over(ledger: &Ledger) -> GraphCard {
        GraphCard::open(
            ledger,
            [0xC9; 32],
            Author(42),
            /*held=*/ AuthRequired::None,
            /*edit_authority=*/ Requirement::AtLeast(Credential::Signature),
        )
    }

    // (a) OPEN — the view is GENERATED from the live ocap web: a header counting cells +
    //     edges, an edges section with the `A → B` row, and a nodes section.
    #[test]
    fn open_generates_a_view_of_the_cap_edges() {
        let (ledger, a, b) = world_with_edge();
        let card = graph_card_over(&ledger);
        let tree = card.view_tree().expect("the generated view parses");

        // Two cells, one edge.
        assert!(
            tree.walk()
                .iter()
                .any(|n| n.label() == Some("Ocap web · 2 cells · 1 edges")),
            "the header counts the live cells + edges"
        );
        assert!(
            tree.walk()
                .iter()
                .any(|n| n.label() == Some("Cap edges (holder → target)")),
            "the edges section is labeled"
        );

        // The `A → B @sig` edge row is rendered (who-can-reach-what).
        let a_short = short_hex(a.as_bytes());
        let b_short = short_hex(b.as_bytes());
        let edge_label = format!("{} → {} @sig", a_short, b_short);
        assert!(
            tree.walk()
                .iter()
                .any(|n| n.label() == Some(edge_label.as_str())),
            "the A → B cap edge is rendered as a row"
        );

        // The edge reads back through the public roster, and reach(A) = {B}.
        let edges = card.edges(&ledger);
        assert_eq!(edges.len(), 1, "exactly one cap edge");
        assert_eq!(edges[0].holder, a);
        assert_eq!(edges[0].target, b);
        let reach = card.reach_of(&ledger, &a);
        assert_eq!(reach, vec![b], "A's multi-hop reach is {{B}}");
    }

    // (b) EDIT FROM WITHIN — relabel a section + append a note: a receipted patch w/ blame.
    #[test]
    fn editing_the_graph_view_from_within_is_a_receipted_patch_with_blame() {
        let (ledger, _, _) = world_with_edge();
        let mut card = graph_card_over(&ledger);
        let source_before = card.view_source();
        let blame_before = card.view_blame().len();

        let edit = card
            .edit_view(ViewPatch::Relabel {
                from: "Cap edges (holder → target)".into(),
                to: "Who can reach what".into(),
            })
            .expect("the authorized relabel reshape is admitted");
        assert_ne!(card.view_source(), source_before, "the view-source changed");
        assert!(
            edit.tree
                .walk()
                .iter()
                .any(|n| n.label() == Some("Who can reach what")),
            "the re-folded view carries the new section label"
        );
        assert_ne!(
            edit.receipt.receipt_hash(),
            [0u8; 32],
            "the structural view-edit left a real provenance receipt on the card's chain"
        );
        assert!(
            card.view_blame().iter().any(|l| l.author == Author(42)),
            "the reshape is blamed on its author"
        );

        let edit2 = card
            .edit_view(ViewPatch::AddButton {
                label: "highlight cycles".into(),
                turn: "highlight_cycles".into(),
                arg: 1,
            })
            .expect("the authorized add-button reshape is admitted");
        assert!(
            edit2.tree.has_button_for("highlight_cycles"),
            "the appended button landed"
        );
        assert!(
            card.view_blame().len() > blame_before,
            "the reshapes added view-source lines (patches, not a recompile)"
        );
        assert_eq!(
            card.card().receipt_count(),
            2,
            "two reshapes → two provenance receipts on the card's chain"
        );
    }

    // (c) the cap tooth — an unauthorized reshape is refused in-band (no patch, no receipt).
    #[test]
    fn an_unauthorized_reshape_is_refused_in_band() {
        let (ledger, _, _) = world_with_edge();
        let mut card = GraphCard::open(
            &ledger,
            [0xBA; 32],
            Author(7),
            /*held=*/ AuthRequired::Signature,
            /*edit_authority=*/ Requirement::AtLeast(Credential::Proof),
        );
        let before = card.view_source();
        let err = card.edit_view(ViewPatch::AddText {
            text: "sneaky".into(),
        });
        assert!(matches!(err, Err(EditError::Unauthorized)));
        assert_eq!(card.view_source(), before, "nothing changed");
        assert_eq!(
            card.card().receipt_count(),
            0,
            "no receipt on an unauthorized reshape"
        );
    }
}
