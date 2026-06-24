//! **THE REFLECTIVE-INSPECTOR CARD** — the cockpit's inspector, reborn as a deos-js card.
//!
//! Today every cockpit surface (the inspector included) is hardcoded Rust gpui: its UI is
//! *compiled code*, so you cannot reshape it without a rebuild and the agent cannot rewrite
//! it. This module makes the inspector a **deos-js card** — a cell whose view is a
//! *view-tree* ([`crate::card_editor::ViewTree`], the same `{kind, props, children}` shape
//! [`deos-view`] renders) generated from a focused cell's **moldable reflective faces**:
//!
//!   - the **RawFields face** ([`deos_reflect::ReflectedCell::raw_fields`]) — the cell's
//!     four-substance state fields, rendered as labeled rows. A scalar state slot becomes a
//!     live [`ViewTree::Bind`] (the renderer re-reads it off the live ledger, so a turn that
//!     writes the slot updates the displayed row); the structural substances (balance,
//!     nonce, caps, lifecycle, …) render as labeled [`ViewTree::Text`].
//!   - the **Affordances face** ([`deos_reflect::AffordanceSurface::project_for`]) — the
//!     focused cell's cap-gated fireable affordances, each a [`ViewTree::Button`] whose click
//!     fires a REAL cap-gated verified turn (a `TurnReceipt`).
//!
//! Because the view is *data* (a view-tree = the card's `view_source` document), it is
//! **editable from within**: [`InspectorCard::edit_view`] patches the inspector card's OWN
//! view-source — relabel a face, add a field row, append a button — as a *receipted patch*
//! with *blame* (who authored each view line, in which patch). The inspector UI reshapes
//! live; the edit is an accountable patch, not a recompile. This is the Pharo-from-within
//! payoff: the real inspector, rewritten from inside, accountably.
//!
//! ## The live World
//!
//! The card's substance is a live verified World — a focused [`Applet`] cell on an embedded
//! [`dregg_sdk::embed::DreggEngine`] ledger. The faces are a pure function of that live
//! ledger ([`deos_reflect`]); a fired affordance is a real verified turn that advances the
//! cell on that same ledger. The inspector card and its focused cell are one sovereign cell
//! (the inspector reflects + reshapes itself — "the image is its own inspector"), so a fired
//! affordance updates a bound field row in place and the card's own view is the thing the
//! edit-from-within rewrites.
//!
//! ## The cap tooth is kept
//!
//! Both teeth are the proven [`dregg_cell::is_attenuation`] gate: a fired affordance is
//! checked against the card's `held` ([`Applet::fire`], in-band), and a view-edit is admitted
//! only when `held` satisfies the card's `edit_authority` ([`InspectorCard::authorized`]).
//! An unauthorized reshape is refused in-band — no patch, no receipt.

use dregg_cell::state::FieldElement;
use dregg_cell::{AuthRequired, CellId, Ledger};
use dregg_doc::{Author, BlameLine};
use dregg_turn::TurnReceipt;

use deos_reflect::present::PresentationBody;
use deos_reflect::substance::FieldValue;
use deos_reflect::{AffordanceSurface, ReflectedCell};

use crate::attach::AttachedApplet;
use crate::applet::{pack_u64, Affordance, Applet, Slot};
use crate::card_editor::{
    BindProps, ButtonProps, EditError, OnClick, TextProps, ViewEdit, ViewPatch, ViewTree,
};
use crate::program_doc::ProgramSource;

/// The heap slot the inspector card bumps to leave a provenance receipt for a *structural*
/// authoring gesture (a view-patch, which does not itself write a model field). Bumping it
/// via a real `SetField` turn is how an edit-from-within still lands a verified receipt on
/// the card's chain — "this inspector's authorship advanced" — alongside the patch + blame.
/// Disjoint from the low model slots a focused cell's fields use.
pub const INSPECTOR_AUTHORSHIP_SLOT: Slot = 14;

/// **The reflective-inspector card** — a deos-js card whose view is a view-tree generated
/// from a focused cell's moldable faces (RawFields + Affordances), rendered over a live
/// World, and editable from within (each edit a receipted patch with blame).
pub struct InspectorCard {
    /// The card's substance: a focused [`Applet`] cell on a live embedded verified World.
    /// Its faces are reflected (the view's DATA); its affordances fire real verified turns;
    /// its own view-source is the thing edit-from-within rewrites.
    card: Applet,
    /// The inspector card's view-source AS A DOCUMENT (a patch-history). The initial view is
    /// generated from the focused cell's faces and seeded here; every edit-from-within
    /// appends a patch, so [`Self::view_blame`] attributes each view line to its author.
    view: ProgramSource,
    /// The authority the inspector card's driver holds — the cap a view-edit is checked
    /// against (the authoring tooth) and the affordance fires are mounted under.
    held: AuthRequired,
    /// The authority a view-edit on THIS card requires (the authoring cap tooth). `held` must
    /// satisfy it ([`dregg_cell::is_attenuation`]).
    edit_authority: AuthRequired,
    /// The author every view-patch is attributed to (the blame identity).
    author: Author,
}

/// One labeled RawFields row, lifted out of the reflected cell into the inspector's view
/// vocabulary: a live-bound scalar slot (a [`ViewTree::Bind`] the renderer re-reads), or a
/// static labeled text for a structural substance.
enum FieldRow {
    /// A scalar state slot — a live binding (`label`: `value`), re-read off the live ledger.
    Bound { label: String, slot: usize },
    /// A structural substance (balance, nonce, caps, lifecycle, an id, a cap edge, …) —
    /// rendered as a static labeled text row.
    Static { text: String },
}

impl InspectorCard {
    /// **Focus the inspector on a card.** `card` is the live focused applet (on an embedded
    /// verified World); `author` attributes the inspector's view-patches; `held` is the
    /// driver's authority and `edit_authority` is the cap a reshape requires.
    ///
    /// The initial view-tree is GENERATED from the focused cell's faces (RawFields rows +
    /// Affordance buttons) and seeded as the card's editable `view_source` document — so the
    /// inspector is a data-defined card from birth, not a hardcoded one.
    pub fn focus(
        card: Applet,
        author: Author,
        held: AuthRequired,
        edit_authority: AuthRequired,
    ) -> Self {
        let initial = generate_view(&card, &held).to_json();
        let view = ProgramSource::seed(author, &initial);
        InspectorCard {
            card,
            view,
            held,
            edit_authority,
            author,
        }
    }

    /// The focused card (read-only) — its model, its receipts, its ledger.
    pub fn card(&self) -> &Applet {
        &self.card
    }

    /// The focused card (mutable) — for firing one of its affordances directly.
    pub fn card_mut(&mut self) -> &mut Applet {
        &mut self.card
    }

    /// Consume the inspector card, yielding its focused [`Applet`] — the live substance a
    /// renderer ([`deos-view`]) drives (a `Bind` row re-reads its model; an affordance
    /// `Button` fires a turn on it). The inspector's current `view_source` is the view-tree
    /// the renderer paints over this applet.
    pub fn into_card(self) -> Applet {
        self.card
    }

    /// The inspector card's current view source (the document fold) — the `view_source` a
    /// renderer parses into a [`deos_view::ViewNode`] tree and paints.
    pub fn view_source(&self) -> String {
        self.view.view_source()
    }

    /// The inspector card's view-tree (the re-folded shape a renderer paints), parsed from
    /// the current view source.
    pub fn view_tree(&self) -> Result<ViewTree, EditError> {
        ViewTree::from_json(&self.view.view_source()).map_err(EditError::BadView)
    }

    /// The blame over the inspector card's view source — who authored each view line, in
    /// which patch (the "accountable patch, not a recompile" face).
    pub fn view_blame(&self) -> Vec<BlameLine> {
        self.view.blame()
    }

    /// **Regenerate** the view-tree from the focused cell's *current* faces, replacing the
    /// view-source as a fresh patch authored by `author`. (Used when the focus changes or to
    /// re-derive the default view; the from-within edits in [`Self::edit_view`] are the
    /// incremental reshape on top of whatever the view currently is.)
    pub fn regenerate_view(&mut self) {
        let fresh = generate_view(&self.card, &self.held).to_json();
        self.view.edit(self.author, &fresh);
    }

    /// Whether the inspector is authorized to reshape itself (the authoring cap tooth).
    fn authorized(&self) -> bool {
        dregg_cell::is_attenuation(&self.held, &self.edit_authority)
    }

    /// Fire a real `SetField` provenance turn bumping the card's authorship slot — how a
    /// *structural* reshape (a view-patch, which does not itself write a model field) still
    /// lands a receipt on the card's chain. Gated on the SAME `edit_authority` the cap tooth
    /// already cleared, so it can only fire when reshaping is authorized.
    fn provenance_turn(&mut self) -> Result<TurnReceipt, EditError> {
        let next = self.card.model().field_u64(INSPECTOR_AUTHORSHIP_SLOT) + 1;
        self.card.register_affordance(Affordance {
            name: "__inspector_authorship__".into(),
            required: self.edit_authority.clone(),
            apply: Box::new(move |_model, _arg| {
                vec![(INSPECTOR_AUTHORSHIP_SLOT, pack_u64(next))]
            }),
        });
        self.card
            .fire("__inspector_authorship__", 0)
            .map_err(|e| EditError::Fire(e.to_string()))
    }

    /// **EDIT THE VIEW FROM WITHIN — the keystone.** Apply a structural reshape (relabel a
    /// face, add a field-row label, append a button) to the inspector card's OWN view-tree,
    /// append the result as a PATCH to the card's `view_source` document, and leave a
    /// provenance receipt on the card's chain.
    ///
    /// The result is the re-folded view-tree (a renderer re-paints it — the inspector UI
    /// reshapes live), the blame (each view line attributed — an *accountable patch, not a
    /// recompile*), and the provenance receipt. Refused in-band if `held` does not satisfy
    /// the card's `edit_authority`, or if the reshape changed nothing.
    pub fn edit_view(&mut self, patch: ViewPatch) -> Result<ViewEdit, EditError> {
        if !self.authorized() {
            return Err(EditError::Unauthorized);
        }

        let mut tree = self.view_tree()?;
        if !apply_patch(&patch, &mut tree) {
            return Err(EditError::NoOp);
        }
        let new_source = tree.to_json();

        // PATCH — append to the view document (NOT a wholesale rewrite), so blame attributes
        // the new lines to this inspector's author.
        self.view.edit(self.author, &new_source);

        // A structural reshape still lands a verified receipt on the card's chain.
        let receipt = self.provenance_turn()?;

        let tree = self.view_tree()?;
        Ok(ViewEdit {
            tree,
            blame: self.view.blame(),
            receipt,
        })
    }

    /// **Fire one of the focused cell's affordances** — commit ONE cap-gated verified turn on
    /// the live World (exactly what a rendered affordance [`ViewTree::Button`]'s click does).
    /// The bound field rows re-read the advanced value on the next render. Bounded by `held`
    /// (the in-band cap tooth in [`Applet::fire`]).
    pub fn fire(&mut self, affordance: &str, arg: i64) -> Result<TurnReceipt, EditError> {
        self.card
            .fire(affordance, arg)
            .map_err(|e| EditError::Fire(e.to_string()))
    }

    /// A witnessed read of a focused-cell model field (so a test can assert a fired
    /// affordance advanced the value the bound row displays).
    pub fn get_u64(&self, slot: Slot) -> u64 {
        self.card.get_u64(slot)
    }
}

/// Apply a [`ViewPatch`] reshape to a view-tree, returning whether it changed anything. (The
/// `card_editor::ViewPatch::apply` is private to that module; this mirrors it for the
/// inspector's own view — append a button / text to the root, or relabel the first matching
/// text.)
fn apply_patch(patch: &ViewPatch, tree: &mut ViewTree) -> bool {
    match patch {
        ViewPatch::AddButton { label, turn, arg } => {
            push_child(
                tree,
                ViewTree::Button {
                    props: ButtonProps {
                        label: label.clone(),
                        on_click: OnClick {
                            turn: turn.clone(),
                            arg: *arg,
                        },
                    },
                },
            )
        }
        ViewPatch::AddText { text } => push_child(
            tree,
            ViewTree::Text {
                props: TextProps { text: text.clone() },
            },
        ),
        ViewPatch::Relabel { from, to } => relabel_text(tree, from, to),
    }
}

/// Push a child onto a container node (vstack/row). Returns whether it landed (false on a
/// leaf).
fn push_child(tree: &mut ViewTree, node: ViewTree) -> bool {
    match tree {
        ViewTree::VStack { children } | ViewTree::Row { children } => {
            children.push(node);
            true
        }
        _ => false,
    }
}

/// Relabel the FIRST text node whose current text equals `from` to `to` (depth-first).
/// Returns whether a node was relabelled.
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

/// **Generate the inspector view-tree** from a focused cell's moldable faces (the embedded
/// [`Applet`] shape — rung 1). Delegates to [`inspector_view_for`], the substance-agnostic
/// core that reads the same RawFields + Affordances faces off any [`Ledger`].
fn generate_view(card: &Applet, held: &AuthRequired) -> ViewTree {
    inspector_view_for(
        card.cell(),
        card.ledger(),
        &card.affordance_specs(),
        held,
    )
}

/// **Generate the inspector view-tree over an ATTACHED LIVE WORLD** — the rung-2 entry.
///
/// The inspector card's view-tree is a pure function of a focused cell's moldable faces;
/// this reads those faces off the cockpit's REAL ledger (through the [`AttachedApplet`]'s
/// [`WorldSink`](crate::attach::WorldSink), the same one a fire commits onto) and the live
/// affordance surface, lifting them into the [`ViewTree`] vocabulary — a `Bind` row per
/// scalar slot (the renderer re-reads it off the live ledger so a landed turn updates it in
/// place) and a cap-gated `Button` per affordance the holder of `held` may fire.
///
/// The returned tree is the inspector card's `view_source`: serialize it
/// ([`ViewTree::to_json`]) and a renderer (`deos-view`) paints it over the live attached
/// applet — the focused cell's faces render live, affordance buttons fire REAL turns, and a
/// bound field updates when a turn lands. This is the additive constructor the cockpit mount
/// uses; the embedded [`InspectorCard::focus`] is kept for the rung-1 tests.
pub fn inspector_view_over_attached(attached: &AttachedApplet, held: &AuthRequired) -> ViewTree {
    let id = attached.cell();
    let specs = attached.affordance_specs();
    let mut tree = ViewTree::root();
    attached.with_ledger(&mut |ledger| {
        tree = inspector_view_for(id, ledger, &specs, held);
    });
    tree
}

/// **The substance-agnostic inspector view-tree core.** Reads the RawFields + Affordances
/// faces of `id` off `ledger` via [`deos_reflect`] and lifts them into the [`ViewTree`]
/// vocabulary: a titled column with a RawFields section (a live `Bind` row per scalar state
/// slot, a labeled `Text` per structural substance) and an Affordances section (a `Button`
/// per cap-gated affordance the holder of `held` may fire). Used over BOTH the embedded
/// [`Applet`] ledger (rung 1) and the cockpit's live attached World (rung 2).
pub fn inspector_view_for(
    id: CellId,
    ledger: &Ledger,
    affordance_specs: &[(String, AuthRequired)],
    held: &AuthRequired,
) -> ViewTree {
    let mut children: Vec<ViewTree> = Vec::new();

    // Title.
    children.push(ViewTree::Text {
        props: TextProps {
            text: "Inspector".into(),
        },
    });

    // ── RawFields face ────────────────────────────────────────────────────────────────
    let mut raw_rows: Vec<ViewTree> = vec![ViewTree::Text {
        props: TextProps {
            text: "Cell State".into(),
        },
    }];
    let rows = ledger.get(&id).map(|cell| {
        let reflected = ReflectedCell {
            id,
            cell: cell.clone(),
        };
        field_rows(&reflected.raw_fields().body)
    });
    if let Some(rows) = rows {
        for row in rows {
            match row {
                FieldRow::Bound { label, slot } => raw_rows.push(ViewTree::Bind {
                    props: BindProps { slot, label },
                }),
                FieldRow::Static { text } => raw_rows.push(ViewTree::Text {
                    props: TextProps { text },
                }),
            }
        }
    }
    children.push(ViewTree::VStack { children: raw_rows });

    // ── Affordances face ──────────────────────────────────────────────────────────────
    let mut aff_rows: Vec<ViewTree> = vec![ViewTree::Text {
        props: TextProps {
            text: "Affordances".into(),
        },
    }];
    let mut surface = AffordanceSurface::new(id);
    for (name, required) in affordance_specs {
        surface = surface.declare(deos_reflect::Affordance::new(
            name.clone(),
            required.clone(),
            dregg_turn::action::Effect::IncrementNonce { cell: id },
        ));
    }
    for aff in surface.project_for(held) {
        aff_rows.push(ViewTree::Button {
            props: ButtonProps {
                label: aff.name.clone(),
                on_click: OnClick {
                    turn: aff.name.clone(),
                    arg: 1,
                },
            },
        });
    }
    children.push(ViewTree::VStack { children: aff_rows });

    ViewTree::VStack { children }
}

/// Lift a RawFields presentation body into inspector view rows. A revealed scalar state slot
/// becomes a live [`FieldRow::Bound`] (the renderer re-reads `(cell, slot)` off the live
/// ledger so a turn updates it); every structural substance (balance, nonce, caps, lifecycle,
/// ids, cap edges, committed/redacted slots) becomes a static labeled text row.
fn field_rows(body: &PresentationBody) -> Vec<FieldRow> {
    let insp = match body {
        PresentationBody::Fields(insp) => insp,
        _ => return Vec::new(),
    };
    let mut out = Vec::new();
    for f in &insp.fields {
        match &f.value {
            // A revealed scalar state slot → a LIVE binding (re-read off the ledger, so a
            // turn that writes the slot updates the displayed row in place).
            FieldValue::FieldSlot { index, .. } => out.push(FieldRow::Bound {
                label: format!("{}: ", f.key),
                slot: *index,
            }),
            // The structural substances render as static labeled text.
            FieldValue::Balance(b) => out.push(FieldRow::Static {
                text: format!("{}: {}", f.key, b),
            }),
            FieldValue::Count(c) => out.push(FieldRow::Static {
                text: format!("{}: {}", f.key, c),
            }),
            FieldValue::Bool(b) => out.push(FieldRow::Static {
                text: format!("{}: {}", f.key, b),
            }),
            FieldValue::Text(t) => out.push(FieldRow::Static {
                text: format!("{}: {}", f.key, t),
            }),
            FieldValue::Id(id) => out.push(FieldRow::Static {
                text: format!("{}: {}", f.key, short_id(id)),
            }),
            FieldValue::Hash(h) => out.push(FieldRow::Static {
                text: format!("{}: {}", f.key, short_id(h)),
            }),
            FieldValue::CapEdge { target, slot } => out.push(FieldRow::Static {
                text: format!("{}: → {} @{}", f.key, short_id(target), slot),
            }),
            FieldValue::CommittedSlot { index, .. } => out.push(FieldRow::Static {
                text: format!("{}: state[{}] ⟨committed⟩", f.key, index),
            }),
        }
    }
    out
}

/// A short legible id (first 6 hex … last 4) for a static field row.
fn short_id(bytes: &[u8; 32]) -> String {
    let h: String = bytes.iter().map(|b| format!("{b:02x}")).collect();
    format!("{}…{}", &h[..6], &h[h.len() - 4..])
}

/// Pack a field element for an inspector model field (re-exported convenience).
pub fn field_value(v: u64) -> FieldElement {
    pack_u64(v)
}
