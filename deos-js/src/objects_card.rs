//! **THE OBJECTS CARD** — the cockpit's OBJECTS surface (the live cell list/grid), reborn
//! as a deos-js card.
//!
//! Today the cockpit's objects surface is hardcoded Rust gpui: its UI is *compiled code*.
//! This module makes it a **deos-js card** — a cell whose view is a *view-tree*
//! ([`crate::card_editor::ViewTree`], the same `{kind, props, children}` shape
//! [`deos-view`] renders) generated from the live World's cell roster:
//!
//!   - the **objects section** — one row per cell on the ledger (id-sorted), each carrying
//!     the cell's short id + its live balance as a labeled [`ViewTree::Text`], plus an
//!     `inspect` [`ViewTree::Button`] (its click is the affordance the cockpit wires to
//!     focusing the inspector on that cell). The roster is a pure function of the live
//!     ledger ([`deos_reflect`] over [`dregg_cell::Ledger`]).
//!
//! Because the view is *data* (a view-tree = the card's `view_source` document), it is
//! **editable from within**: [`ObjectsCard::edit_view`] patches the objects card's OWN
//! view-source — relabel a header, add a filter button, append a note — as a *receipted
//! patch* with *blame*. The edit lands a real provenance receipt on the card's OWN cell's
//! chain (the same [`Applet`]-backed authorship turn the inspector card uses), so a reshape
//! is an accountable patch, not a recompile.
//!
//! ## The live World
//!
//! The objects card reflects over a PROVIDED ledger (the cockpit's real World, or an
//! embedded [`Applet`]'s single-cell world for the rung-1 tests) — the data is the live
//! roster, never a parallel copy. The card itself is one sovereign cell (its own [`Applet`]),
//! so an edit-from-within receipts on its chain exactly as the inspector card does.
//!
//! ## The cap tooth is kept
//!
//! A view-edit is admitted only when `held` satisfies the card's `edit_authority`
//! ([`ObjectsCard::authorized`], the proven [`dregg_cell::is_attenuation`] gate). An
//! unauthorized reshape is refused in-band — no patch, no receipt.

use dregg_cell::{AuthRequired, Ledger};
use dregg_doc::{Author, BlameLine};
use dregg_turn::TurnReceipt;
use dregg_types::CellId;

use deos_reflect::substance::{lifecycle_label, short_hex};

use crate::applet::{pack_u64, Affordance, Applet, Slot};
use crate::card_editor::{
    ButtonProps, EditError, OnClick, TextProps, ViewEdit, ViewPatch, ViewTree,
};
use crate::program_doc::ProgramSource;
use dregg_cell::{Credential, Requirement};

/// The heap slot the objects card bumps to leave a provenance receipt for a *structural*
/// authoring gesture (a view-patch, which does not itself write a model field). Disjoint
/// from the inspector card's authorship slot so a cockpit hosting both does not collide.
pub const OBJECTS_AUTHORSHIP_SLOT: Slot = 16;

/// One object row as the card reads it back: a cell, its short id, and its live balance —
/// the row the view renders (id + balance) and an `inspect` affordance fires against.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ObjectRow {
    /// The cell this row stands for.
    pub cell: CellId,
    /// A short operator-legible id.
    pub short: String,
    /// The cell's live balance (an issuer well carries −supply).
    pub balance: i64,
    /// The cell's lifecycle label.
    pub lifecycle: String,
}

/// **The objects card** — a deos-js card whose view is a view-tree generated from the live
/// World's cell roster (a row per cell: short id + balance + an `inspect` button), reflected
/// over a provided ledger, and editable from within (each reshape a receipted patch).
pub struct ObjectsCard {
    /// The card's OWN sovereign cell — the substance an edit-from-within receipts against
    /// (its authorship slot bumps via a real `SetField` turn). NOT the cells it lists.
    card: Applet,
    /// The objects card's view-source AS A DOCUMENT (a patch-history). The initial view is
    /// generated from the roster; every edit-from-within appends a patch.
    view: ProgramSource,
    /// The authority the card's driver holds — the cap a view-edit is checked against.
    held: AuthRequired,
    /// The authority a view-edit on THIS card requires (the authoring cap tooth).
    edit_authority: Requirement,
    /// The author every view-patch is attributed to (the blame identity).
    author: Author,
}

impl ObjectsCard {
    /// **Open an objects card** over a live World (`ledger`), authored by `author`. `held`
    /// is the driver's authority and `edit_authority` the cap a view-reshape requires. The
    /// initial view-tree is GENERATED from the ledger's cell roster and seeded as the
    /// card's editable `view_source` document. The card mints its OWN cell from `card_pk`
    /// (the provenance substance).
    pub fn open(
        ledger: &Ledger,
        card_pk: [u8; 32],
        author: Author,
        held: AuthRequired,
        edit_authority: Requirement,
    ) -> Self {
        let card = Applet::mint(card_pk, [0u8; 32], &[], Vec::new(), held.clone());
        let initial = objects_view_for(ledger).to_json();
        let view = ProgramSource::seed(author, &initial);
        ObjectsCard {
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

    /// The objects card's current view source (the document fold).
    pub fn view_source(&self) -> String {
        self.view.view_source()
    }

    /// The objects card's view-tree (the re-folded shape a renderer paints).
    pub fn view_tree(&self) -> Result<ViewTree, EditError> {
        ViewTree::from_json(&self.view.view_source()).map_err(EditError::BadView)
    }

    /// The blame over the objects card's view source — who authored each view line.
    pub fn view_blame(&self) -> Vec<BlameLine> {
        self.view.blame()
    }

    /// **The object roster** — one [`ObjectRow`] per cell on `ledger`, id-sorted. The
    /// view's DATA (a pure function of the live ledger).
    pub fn roster(&self, ledger: &Ledger) -> Vec<ObjectRow> {
        object_rows(ledger)
    }

    /// **Regenerate** the view-tree from the live ledger's *current* roster, replacing the
    /// view-source as a fresh patch (used when the World advances — a spawned/destroyed
    /// cell changes the list). The from-within edits in [`Self::edit_view`] reshape on top.
    pub fn regenerate_view(&mut self, ledger: &Ledger) {
        let fresh = objects_view_for(ledger).to_json();
        self.view.edit(self.author, &fresh);
    }

    /// Whether the card is authorized to reshape its own view (the authoring cap tooth).
    fn authorized(&self) -> bool {
        self.edit_authority.satisfied_by(&self.held)
    }

    /// Fire a real `SetField` provenance turn bumping the card's authorship slot — how a
    /// *structural* reshape lands a receipt on the card's chain.
    fn provenance_turn(&mut self) -> Result<TurnReceipt, EditError> {
        let next = self.card.model().field_u64(OBJECTS_AUTHORSHIP_SLOT) + 1;
        self.card.register_affordance(Affordance {
            name: "__objects_authorship__".into(),
            required: self.edit_authority.clone(),
            apply: Box::new(move |_model, _arg| vec![(OBJECTS_AUTHORSHIP_SLOT, pack_u64(next))]),
        });
        self.card
            .fire("__objects_authorship__", 0)
            .map_err(|e| EditError::Fire(e.to_string()))
    }

    /// **EDIT THE VIEW FROM WITHIN — the keystone.** Apply a structural reshape (relabel a
    /// header, add a button, append a note) to the objects card's OWN view-tree, append the
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

// ── view-tree generation (the objects card's view IS the live roster's data) ────────────

/// **Generate the objects view-tree** from a live ledger: a titled column with a header
/// row + one row per cell (short id + balance label + an `inspect` button). The
/// substance-agnostic core both [`ObjectsCard::open`] and the public [`objects_view`] use.
fn objects_view_for(ledger: &Ledger) -> ViewTree {
    objects_view_for_rows(&object_rows(ledger))
}

/// Lift an object-row list into the objects card's view vocabulary.
fn objects_view_for_rows(rows: &[ObjectRow]) -> ViewTree {
    let mut top: Vec<ViewTree> = Vec::new();
    top.push(text(&format!("Objects · {} cells", rows.len())));

    let mut list: Vec<ViewTree> = vec![text("Cells")];
    if rows.is_empty() {
        list.push(text("(no cells)"));
    } else {
        for row in rows {
            // Each cell is a row: a labeled id+balance text and an `inspect` affordance
            // whose click the cockpit wires to focusing the inspector on this cell.
            list.push(ViewTree::Row {
                children: vec![
                    text(&format!("{} · bal {}", row.short, row.balance)),
                    button(
                        "inspect",
                        &format!("inspect:{}", short_hex(row.cell.as_bytes())),
                        1,
                    ),
                ],
            });
        }
    }
    top.push(ViewTree::VStack { children: list });

    ViewTree::VStack { children: top }
}

/// **Generate the objects view-tree (the public entry).** A renderer (`deos-view`) parses
/// the JSON of this and paints it over the objects card; the per-cell `inspect` buttons
/// map to focusing the inspector, the rows to the live cell roster.
pub fn objects_view(ledger: &Ledger) -> ViewTree {
    objects_view_for(ledger)
}

/// **The object rows** off a live ledger: one per cell, id-sorted, carrying the cell's
/// short id, live balance, and lifecycle.
pub fn object_rows(ledger: &Ledger) -> Vec<ObjectRow> {
    let mut cells: Vec<(CellId, ObjectRow)> = ledger
        .iter()
        .map(|(id, cell)| {
            (
                *id,
                ObjectRow {
                    cell: *id,
                    short: short_hex(id.as_bytes()),
                    balance: cell.state.balance(),
                    lifecycle: lifecycle_label(cell),
                },
            )
        })
        .collect();
    cells.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));
    cells.into_iter().map(|(_, row)| row).collect()
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

    /// A small World: an embedded applet's ledger seeded with a balance (so the row shows a
    /// real balance). The objects card reflects over THIS ledger.
    fn world(seed: u8) -> Applet {
        let mut pk = [0u8; 32];
        pk[0] = seed;
        Applet::mint(
            pk,
            [0u8; 32],
            &[(0usize, pack_u64(1))],
            Vec::new(),
            AuthRequired::None,
        )
    }

    fn objects_card_over(world: &Applet) -> ObjectsCard {
        ObjectsCard::open(
            world.ledger(),
            [0xCA; 32],
            Author(42),
            /*held=*/ AuthRequired::None,
            /*edit_authority=*/ Requirement::AtLeast(Credential::Signature),
        )
    }

    // (a) OPEN — the view is GENERATED from the live ledger's roster: a header + a row per
    //     cell, each with an `inspect` affordance.
    #[test]
    fn open_generates_a_view_with_a_row_per_cell_and_an_inspect_affordance() {
        let w = world(0xAB);
        let card = objects_card_over(&w);
        let tree = card.view_tree().expect("the generated view parses");

        // The world's single cell shows up as a row with an `inspect` button.
        let id = w.cell();
        let inspect_turn = format!("inspect:{}", short_hex(id.as_bytes()));
        assert!(
            tree.has_button_for(&inspect_turn),
            "the objects view carries an `inspect` affordance for the cell"
        );
        assert!(
            tree.walk().iter().any(|n| n.label() == Some("Cells")),
            "the objects section is labeled"
        );
        // The roster reads back the cell with its real balance.
        let rows = card.roster(w.ledger());
        assert_eq!(rows.len(), 1, "one cell on this world");
        assert_eq!(rows[0].cell, id);
        assert!(rows[0].balance > 0, "the cell's live balance reads back");
        // The header counts the cells.
        assert!(
            tree.walk()
                .iter()
                .any(|n| n.label() == Some("Objects · 1 cells")),
            "the header counts the live roster"
        );
    }

    // (b) EDIT FROM WITHIN — relabel the header + append a note: a receipted patch w/ blame.
    #[test]
    fn editing_the_objects_view_from_within_is_a_receipted_patch_with_blame() {
        let w = world(0xCD);
        let mut card = objects_card_over(&w);
        let source_before = card.view_source();
        let blame_before = card.view_blame().len();

        let edit = card
            .edit_view(ViewPatch::Relabel {
                from: "Cells".into(),
                to: "Sovereign cells".into(),
            })
            .expect("the authorized relabel reshape is admitted");
        assert_ne!(card.view_source(), source_before, "the view-source changed");
        assert!(
            edit.tree
                .walk()
                .iter()
                .any(|n| n.label() == Some("Sovereign cells")),
            "the re-folded view carries the new header label"
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
                label: "refresh".into(),
                turn: "refresh".into(),
                arg: 1,
            })
            .expect("the authorized add-button reshape is admitted");
        assert!(
            edit2.tree.has_button_for("refresh"),
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
        let w = world(0xEF);
        let mut card = ObjectsCard::open(
            w.ledger(),
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
