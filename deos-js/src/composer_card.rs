//! **THE COMPOSER CARD** — the cockpit's document composer, reborn as a deos-js card.
//!
//! Today the composer surface (`starbridge-v2/src/document_composer.rs`) is a gpui-free
//! logic core, but its *view* is hardcoded cockpit Rust: you compose a document from cells
//! by hand, yet the surface itself is compiled code you cannot reshape from within. This
//! module makes the composer a **deos-js card** — a cell whose view is a *view-tree*
//! ([`crate::card_editor::ViewTree`], the same `{kind, props, children}` shape
//! [`deos-view`] renders) generated from the document's live composition:
//!
//!   - the **composed-children section** — one labeled [`ViewTree::Text`] row per live
//!     embed (its short cell id + role), in document order, read back through the REAL
//!     membrane-gated fold ([`dregg_doc::composition::content_composed`]). A removed child
//!     is tombstoned (gone from the live render, retained + provenanced in the roster).
//!   - the **gestures section** — the four composition gestures as [`ViewTree::Button`]s
//!     (add embed / reorder / remove / set-role), each firing a REAL composition patch on
//!     the document cell ([`LayoutGraph::apply_patch`], which stamps the authoring
//!     [`Author`]'s [`Provenance`] — the receipt the document commitment binds).
//!
//! Because the view is *data* (a view-tree = the card's `view_source` document), it is
//! **editable from within**: [`ComposerCard::edit_view`] patches the composer card's OWN
//! view-source — relabel a section, add a gesture button, append a note — as a *receipted
//! patch* with *blame* (who authored each view line, in which patch). The composer UI
//! reshapes live; the edit is an accountable patch, not a recompile.
//!
//! ## It is the SAME machinery, pointed at authoring
//!
//! A composed document is a [`dregg_doc::composition::LayoutGraph`]: a graph of embed-atoms
//! (cell-pointers) plus order-edges, driven by exactly four ops ([`Op::Embed`] /
//! [`Op::Order`] / [`Op::Remove`]). The composer card reuses that algebra VERBATIM (no
//! parallel model), exactly as the cockpit `document_composer` does — this is the
//! *reflective* face onto it: the composition's live state IS the view's data, and the four
//! gestures are buttons whose clicks fire the ops.
//!
//! ## The cap tooth is kept
//!
//! A view-edit is admitted only when `held` satisfies the card's `edit_authority`
//! ([`ComposerCard::authorized`], the proven [`dregg_cell::is_attenuation`] gate). An
//! unauthorized reshape is refused in-band — no patch, no receipt.

use dregg_cell::AuthRequired;
use dregg_doc::composition::{
    self, content_composed, AtomContent, ChildRef, EmbedRole, LayoutGraph, MapResolver, Op, Viewer,
};
use dregg_doc::{AtomId, Author, BlameLine, PatchId, Provenance, Status};

use crate::card_editor::{ButtonProps, EditError, OnClick, TextProps, ViewPatch, ViewTree};
use crate::program_doc::ProgramSource;

pub use dregg_doc::composition::CellId as ChildCellId;

/// The seed domain for composer embed-atom ids — keyed on the CHILD CELL ONLY (not the
/// role), so the child's embed-atom identity is STABLE across a role change (a re-role
/// tombstones the old role-atom and embeds a fresh one, both addressed from this same
/// `(seed, cell)` derivation). Matches the cockpit `document_composer`'s seed so a card
/// adopting a cockpit-authored layout addresses the same atoms.
const COMPOSER_EMBED_SEED: u64 = 0xC0_4905_E1ED; // "composed"

/// The role an embedded child plays in the composed document — a thin, exhaustive mirror
/// of [`EmbedRole`] so the composer card's public surface does not leak the `dregg_doc`
/// enum.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Role {
    /// A whole section.
    Section,
    /// A figure / illustration.
    Figure,
    /// An inline span.
    Inline,
    /// A block (e.g. the focused / active child).
    Block,
    /// A live cited cell (a citation that is itself a cell, not a value-quote).
    Citation,
}

impl Role {
    fn to_embed(self) -> EmbedRole {
        match self {
            Role::Section => EmbedRole::Section,
            Role::Figure => EmbedRole::Figure,
            Role::Inline => EmbedRole::Inline,
            Role::Block => EmbedRole::Block,
            Role::Citation => EmbedRole::Citation,
        }
    }

    fn from_embed(r: EmbedRole) -> Self {
        match r {
            EmbedRole::Section => Role::Section,
            EmbedRole::Figure => Role::Figure,
            EmbedRole::Inline => Role::Inline,
            EmbedRole::Block => Role::Block,
            EmbedRole::Citation => Role::Citation,
        }
    }

    fn slug(self) -> &'static str {
        match self {
            Role::Section => "section",
            Role::Figure => "figure",
            Role::Inline => "inline",
            Role::Block => "block",
            Role::Citation => "citation",
        }
    }
}

/// The receipt a composition gesture leaves — the [`Provenance`] the layout stamped onto
/// the atom(s) the gesture wrote (author + the content-derived [`PatchId`]). On the
/// substrate this IS the turn's receipt: a verifiable record that THIS author made THIS
/// edit to the document cell.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Receipt {
    /// Who authored the gesture.
    pub author: Author,
    /// The content-derived patch id (the turn's receipt id).
    pub patch: PatchId,
}

impl Receipt {
    fn from_prov(p: Provenance) -> Self {
        Receipt {
            author: p.author,
            patch: p.patch,
        }
    }

    /// Whether this receipt is non-empty (a real gesture landed a patch) — the composer's
    /// analogue of "a non-zero receipt hash". A GENESIS patch is the empty fallback.
    pub fn is_landed(&self) -> bool {
        self.patch != PatchId::GENESIS
    }
}

/// The record of a successful composer view-reshape: the re-folded view-tree, the blame
/// (each view line attributed — the "accountable patch, not a recompile" face), and the
/// composition [`Receipt`] the structural edit left on the document cell's composition.
///
/// Distinct from [`crate::card_editor::ViewEdit`] (which carries a state-machine
/// [`dregg_turn::TurnReceipt`]): a composer card's chain is the document's COMPOSITION, so
/// its receipt is a [`Provenance`] / [`PatchId`], not a turn — the honest record.
pub struct ComposerViewEdit {
    /// The re-folded view-tree a renderer re-paints.
    pub tree: ViewTree,
    /// The blame over the view source — who authored each view line, in which patch.
    pub blame: Vec<BlameLine>,
    /// The composition receipt the structural reshape left on the document cell.
    pub receipt: Receipt,
}

/// One composed child as the composer reads it back: which cell, at what role, who placed
/// it, and whether it is currently live (a removed child is tombstoned — gone from the
/// render but its citation + provenance survive).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ComposedChild {
    /// The embedded child cell (the citation — always present, even when removed).
    pub cell: ChildCellId,
    /// The embed-atom id (stable per child across a role change — the order target).
    pub atom: AtomId,
    /// The role the child currently plays.
    pub role: Role,
    /// Who placed this child (the surviving provenance — never forged).
    pub placed_by: Author,
    /// Whether the child is live in the rendered document.
    pub live: bool,
}

/// **The composer card** — a deos-js card whose view is a view-tree generated from a
/// document cell's live composition (the composed-children list + the four gesture
/// buttons), driven by the REAL [`dregg_doc::composition`] algebra, and editable from
/// within (each view-edit a receipted patch with blame).
pub struct ComposerCard {
    /// The document cell this composer authors (the host of the composition).
    host: ChildCellId,
    /// The composition layout graph — embed-atoms + order-edges (the REAL model the four
    /// gestures drive, reused verbatim from [`dregg_doc::composition`]).
    layout: LayoutGraph,
    /// The running predecessor for the NEXT add (the tail of the current chain), so a run
    /// of [`Self::add_embed`]s appends in order without the caller threading anchors.
    tail: AtomId,
    /// The composer card's view-source AS A DOCUMENT (a patch-history). The initial view
    /// is generated from the composition; every edit-from-within appends a patch.
    view: ProgramSource,
    /// The authority the composer card's driver holds — the cap a view-edit is checked
    /// against (the authoring tooth).
    held: AuthRequired,
    /// The authority a view-edit on THIS card requires (the authoring cap tooth).
    edit_authority: AuthRequired,
    /// The author every gesture + view-patch is attributed to (the blame identity).
    author: Author,
}

impl ComposerCard {
    /// **Open a composer card** over an empty document cell `host`, authored by `author`.
    /// `held` is the driver's authority and `edit_authority` is the cap a view-reshape
    /// requires. The initial view-tree is GENERATED from the (empty) composition and
    /// seeded as the card's editable `view_source` document.
    pub fn open(
        host: ChildCellId,
        author: Author,
        held: AuthRequired,
        edit_authority: AuthRequired,
    ) -> Self {
        let layout = LayoutGraph::new();
        let initial = composer_view_for(host, &layout).to_json();
        let view = ProgramSource::seed(author, &initial);
        ComposerCard {
            host,
            layout,
            tail: AtomId::ROOT,
            view,
            held,
            edit_authority,
            author,
        }
    }

    /// The document cell this composer authors.
    pub fn host(&self) -> ChildCellId {
        self.host
    }

    /// The authoring identity.
    pub fn author(&self) -> Author {
        self.author
    }

    /// Read-only access to the underlying composition layout (for inspection / merge /
    /// time-travel / projecting through a different viewer).
    pub fn layout(&self) -> &LayoutGraph {
        &self.layout
    }

    /// The composer card's current view source (the document fold) — a renderer parses
    /// this into a [`deos_view::ViewNode`] tree and paints it.
    pub fn view_source(&self) -> String {
        self.view.view_source()
    }

    /// The composer card's view-tree (the re-folded shape a renderer paints).
    pub fn view_tree(&self) -> Result<ViewTree, EditError> {
        ViewTree::from_json(&self.view.view_source()).map_err(EditError::BadView)
    }

    /// The blame over the composer card's view source — who authored each view line, in
    /// which patch (the "accountable patch, not a recompile" face).
    pub fn view_blame(&self) -> Vec<BlameLine> {
        self.view.blame()
    }

    /// The embed-atom id `cell` is placed at (the initial-placement id, keyed on the
    /// cell). A later reorder / remove can target this directly — UNTIL a [`Self::set_role`]
    /// re-roles the cell. For a target robust across a re-role, use [`Self::live_atom`].
    pub fn embed_id(&self, cell: ChildCellId) -> AtomId {
        AtomId::derive(COMPOSER_EMBED_SEED, &format!("embed:{}", cell.0))
    }

    /// The CURRENT live embed-atom id for `cell` (robust across a re-role). `None` if
    /// `cell` is not a live child.
    pub fn live_atom(&self, cell: ChildCellId) -> Option<AtomId> {
        embed_atoms(&self.layout)
            .into_iter()
            .find(|(id, _, c, _)| *c == cell && is_alive(&self.layout, *id))
            .map(|(id, _, _, _)| id)
    }

    // ── the four gestures (each a REAL composition patch on the document cell) ──────────

    /// **ADD AN EMBED** — place `cell` as a child of the document, in `role`, appended
    /// after the current tail (an [`Op::Embed`]). Returns the gesture's [`Receipt`].
    pub fn add_embed(&mut self, cell: ChildCellId, role: Role) -> Receipt {
        let id = self.embed_id(cell);
        let after = self.tail;
        self.apply(&[Op::Embed {
            id,
            child: ChildRef::live(cell),
            after,
            role: role.to_embed(),
        }]);
        self.tail = id;
        self.regenerate_view();
        self.receipt_of(id)
    }

    /// **ADD AN EMBED AT A FORK** — place `cell` anchored after `after_cell` (or the HEAD
    /// if `None`) WITHOUT advancing the append tail. Two children at the SAME anchor form
    /// a layout fork (an antichain) which [`Self::reorder`] resolves. Returns the [`Receipt`].
    pub fn add_embed_at(
        &mut self,
        cell: ChildCellId,
        after_cell: Option<ChildCellId>,
        role: Role,
    ) -> Receipt {
        let id = self.embed_id(cell);
        let after = match after_cell {
            Some(target) => self.live_atom(target).unwrap_or(AtomId::ROOT),
            None => AtomId::ROOT,
        };
        self.apply(&[Op::Embed {
            id,
            child: ChildRef::live(cell),
            after,
            role: role.to_embed(),
        }]);
        self.regenerate_view();
        self.receipt_of(id)
    }

    /// **REORDER** — add the order constraint "`child` comes after `before`" (an
    /// [`Op::Order`]). Pass [`AtomId::ROOT`] as `before` to constrain `child` to the head.
    /// Returns the [`Receipt`].
    pub fn reorder(&mut self, child: AtomId, before: AtomId) -> Receipt {
        self.apply(&[Op::Order {
            from: before,
            to: child,
        }]);
        self.regenerate_view();
        self.receipt_of(child)
    }

    /// **REMOVE** — tombstone the embed-atom `child` (an [`Op::Remove`]: monotone
    /// `Alive -> Dead`). The child drops off [`Self::children`] but is RETAINED + provenanced
    /// in [`Self::roster`]. Returns the [`Receipt`].
    pub fn remove(&mut self, child: AtomId) -> Receipt {
        self.apply(&[Op::Remove { id: child }]);
        if self.tail == child {
            self.tail = last_live_atom(&self.layout);
        }
        self.regenerate_view();
        self.receipt_of(child)
    }

    /// **SET A CHILD'S ROLE** — change the role `cell` plays. Tombstones the old role-atom
    /// and embeds a FRESH one for the SAME cell at the SAME anchor (citation + order
    /// preserved; only the role reads back changed). `None` if `cell` is not a live child.
    pub fn set_role(&mut self, cell: ChildCellId, role: Role) -> Option<Receipt> {
        let id = self.embed_id(cell);
        let atom = self.layout.atom(id)?;
        if !atom.is_alive() {
            return None;
        }
        let after = predecessor_of(&self.layout, id);
        let new_id = AtomId::derive(
            COMPOSER_EMBED_SEED,
            &format!("embed:{}:role:{:?}", cell.0, role.to_embed()),
        );
        self.apply(&[
            Op::Remove { id },
            Op::Embed {
                id: new_id,
                child: ChildRef::live(cell),
                after,
                role: role.to_embed(),
            },
        ]);
        if self.tail == id {
            self.tail = new_id;
        }
        self.regenerate_view();
        Some(self.receipt_of(new_id))
    }

    // ── the composed reading (the view's DATA) ──────────────────────────────────────────

    /// **THE COMPOSED CHILD LIST** — the live children in document order, each with its
    /// cell, role, and who placed it. Read through the REAL membrane-gated fold over a
    /// viewer that clears every embedded cell (the author's full-authority read).
    pub fn children(&self) -> Vec<ComposedChild> {
        let viewer = self.full_authority_viewer();
        let resolver = self.resolver();
        let rendered = content_composed(&self.layout, &viewer, &resolver);
        children_of(&rendered, &self.layout)
    }

    /// The full ROSTER — every embed-atom ever placed, live OR tombstoned (the
    /// time-travellable record). A removed child appears marked `live: false`.
    pub fn roster(&self) -> Vec<ComposedChild> {
        let live = self.children();
        let mut out = live.clone();
        let live_atoms: std::collections::BTreeSet<AtomId> = live.iter().map(|c| c.atom).collect();
        for (id, role, cell, prov) in embed_atoms(&self.layout) {
            if !live_atoms.contains(&id) {
                out.push(ComposedChild {
                    cell,
                    atom: id,
                    role: Role::from_embed(role),
                    placed_by: prov.author,
                    live: false,
                });
            }
        }
        out
    }

    // ── edit-from-within (the reflective keystone) ──────────────────────────────────────

    /// **Regenerate** the view-tree from the composition's *current* state, replacing the
    /// view-source as a fresh patch authored by `author`. Called after every gesture so the
    /// composed-children section tracks the live composition; the from-within edits in
    /// [`Self::edit_view`] are the incremental reshape on top.
    pub fn regenerate_view(&mut self) {
        let fresh = composer_view_for_children(self.host, &self.children()).to_json();
        self.view.edit(self.author, &fresh);
    }

    /// Whether the composer is authorized to reshape its own view (the authoring cap tooth).
    fn authorized(&self) -> bool {
        dregg_cell::is_attenuation(&self.held, &self.edit_authority)
    }

    /// **EDIT THE VIEW FROM WITHIN — the keystone.** Apply a structural reshape (relabel a
    /// section, add a gesture button, append a note) to the composer card's OWN view-tree
    /// and append the result as a PATCH to the card's `view_source` document with blame.
    /// Refused in-band if `held` does not satisfy `edit_authority`, or if it changed nothing.
    ///
    /// The receipt is the composition's own gesture receipt: bumping the composer card's
    /// view authorship lands a real composition patch (a [`Provenance`]) on the document
    /// cell's chain — "this composer's authorship advanced" — so a view-reshape is never
    /// silent. (A structural reshape carries a provenance like any gesture.)
    pub fn edit_view(&mut self, patch: ViewPatch) -> Result<ComposerViewEdit, EditError> {
        if !self.authorized() {
            return Err(EditError::Unauthorized);
        }
        let mut tree = self.view_tree()?;
        if !apply_view_patch(&patch, &mut tree) {
            return Err(EditError::NoOp);
        }
        let new_source = tree.to_json();
        self.view.edit(self.author, &new_source);

        // A structural reshape still leaves a verified provenance on the document cell's
        // composition — a dedicated authorship atom keyed on the running patch count.
        let receipt = self.provenance_gesture();

        let tree = self.view_tree()?;
        Ok(ComposerViewEdit {
            tree,
            blame: self.view.blame(),
            receipt,
        })
    }

    // ── internals ────────────────────────────────────────────────────────────────────

    /// Apply a gesture's ops to the layout under the composer's author (the REAL
    /// composition `apply_patch`, which stamps provenance = author + content-derived id).
    fn apply(&mut self, ops: &[Op]) {
        self.layout.apply_patch(self.author, ops);
    }

    /// The receipt an atom carries after a gesture — the provenance the layout stamped.
    fn receipt_of(&self, id: AtomId) -> Receipt {
        match self.layout.atom(id) {
            Some(a) => Receipt::from_prov(a.provenance),
            None => Receipt {
                author: self.author,
                patch: PatchId::GENESIS,
            },
        }
    }

    /// Land a provenance gesture for a structural view-reshape: a dedicated authorship
    /// embed-atom (gone immediately — tombstoned), keyed on the live patch count, so each
    /// reshape leaves a fresh, distinct provenance on the document cell's composition.
    fn provenance_gesture(&mut self) -> Receipt {
        let n = embed_atoms(&self.layout).len() as u128;
        let id = AtomId::derive(
            COMPOSER_EMBED_SEED,
            &format!("view-authorship:{}:{}", self.host.0, n),
        );
        self.apply(&[
            Op::Embed {
                id,
                child: ChildRef::live(ChildCellId(self.host.0 ^ 0x0A07_4015_4109)),
                after: AtomId::ROOT,
                role: EmbedRole::Inline,
            },
            Op::Remove { id },
        ]);
        self.receipt_of(id)
    }

    /// A viewer that clears every embedded cell (the owning author's full-authority read).
    fn full_authority_viewer(&self) -> Viewer {
        Viewer::able(
            embed_atoms(&self.layout)
                .into_iter()
                .map(|(_, _, cell, _)| cell),
        )
    }

    /// A resolver that renders each embedded cell as a one-atom leaf (the standalone shape).
    fn resolver(&self) -> MapResolver {
        let mut r = MapResolver::default();
        for (_, _, cell, _) in embed_atoms(&self.layout) {
            let mut g = LayoutGraph::new();
            let marker = AtomId::derive(0xC0_4EAF, &format!("content:{}", cell.0));
            g.insert_atom(composition::LayoutAtom {
                id: marker,
                content: AtomContent::Text(format!("cell {:x}", cell.0)),
                status: Status::Alive,
                provenance: Provenance::GENESIS,
            });
            g.connect_pub(AtomId::ROOT, marker);
            r = r.with(cell, g);
        }
        r
    }
}

/// The render for an arbitrary `viewer` — the per-viewer membrane (an out-of-cap child
/// DARKENS — citation kept, content withheld — never forged). Standalone helper so a test
/// can assert the shareable reading without exposing the resolver.
pub fn composer_render_for(card: &ComposerCard, viewer: &Viewer) -> composition::Rendered {
    content_composed(&card.layout, viewer, &card.resolver())
}

// ── view-tree generation (the composer card's view IS its composition's data) ──────────

/// **Generate the composer view-tree** from a document cell's live composition: a titled
/// column with a composed-children section (a labeled row per live embed) + a gestures
/// section (the four composition gestures as buttons). Reads the children through the REAL
/// fold; used at [`ComposerCard::open`] and on every regenerate.
fn composer_view_for(host: ChildCellId, layout: &LayoutGraph) -> ViewTree {
    let viewer = Viewer::able(embed_atoms(layout).into_iter().map(|(_, _, c, _)| c));
    let mut resolver = MapResolver::default();
    for (_, _, cell, _) in embed_atoms(layout) {
        let mut g = LayoutGraph::new();
        let marker = AtomId::derive(0xC0_4EAF, &format!("content:{}", cell.0));
        g.insert_atom(composition::LayoutAtom {
            id: marker,
            content: AtomContent::Text(format!("cell {:x}", cell.0)),
            status: Status::Alive,
            provenance: Provenance::GENESIS,
        });
        g.connect_pub(AtomId::ROOT, marker);
        resolver = resolver.with(cell, g);
    }
    let rendered = content_composed(layout, &viewer, &resolver);
    let children = children_of(&rendered, layout);
    composer_view_for_children(host, &children)
}

/// Lift a composed-children list into the composer card's view vocabulary: a titled column
/// with a composed-children section (a `Text` row per live embed) + the four gesture
/// buttons. The substance-agnostic core both [`composer_view_for`] and
/// [`ComposerCard::regenerate_view`] use.
fn composer_view_for_children(host: ChildCellId, children: &[ComposedChild]) -> ViewTree {
    let mut top: Vec<ViewTree> = Vec::new();

    // Title.
    top.push(text(&format!("Composer · doc {:x}", host.0)));

    // ── Composed children section ───────────────────────────────────────────────────
    let mut kids: Vec<ViewTree> = vec![text("Composed cells")];
    if children.is_empty() {
        kids.push(text("(empty — add an embed)"));
    } else {
        for (i, c) in children.iter().enumerate() {
            kids.push(text(&format!(
                "{}. {} · {}",
                i + 1,
                short_cell(c.cell),
                c.role.slug()
            )));
        }
    }
    top.push(ViewTree::VStack { children: kids });

    // ── Gestures section ────────────────────────────────────────────────────────────
    let gestures = vec![
        text("Gestures"),
        button("add embed", "add_embed", 1),
        button("reorder", "reorder", 1),
        button("remove", "remove", 1),
        button("set role", "set_role", 1),
    ];
    top.push(ViewTree::VStack { children: gestures });

    ViewTree::VStack { children: top }
}

/// **Generate the composer view-tree (the public entry).** A renderer (`deos-view`)
/// parses the JSON of this and paints it over the composer card; the gesture buttons map
/// to the four composition ops, the composed rows to the live children.
pub fn composer_view(card: &ComposerCard) -> ViewTree {
    composer_view_for_children(card.host, &card.children())
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

/// A short legible cell id for a composed row.
fn short_cell(c: ChildCellId) -> String {
    let h = format!("{:032x}", c.0);
    format!("{}…{}", &h[..6], &h[h.len() - 4..])
}

// ── the view-patch reshape (mirrors the inspector card's, since `ViewPatch::apply` is
//    private to `card_editor`) ──────────────────────────────────────────────────────────

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

// ── composition graph helpers (verbatim shape from the cockpit composer) ────────────────

fn children_of(rendered: &composition::Rendered, layout: &LayoutGraph) -> Vec<ComposedChild> {
    let mut out = Vec::new();
    for seg in &rendered.segments {
        if let composition::Segment::Embedded {
            role,
            placed_by,
            resolved_cell: Some(cell),
            ..
        } = seg
        {
            let atom = embed_atoms(layout)
                .into_iter()
                .find(|(id, _, c, _)| *c == *cell && is_alive(layout, *id))
                .map(|(id, _, _, _)| id)
                .unwrap_or(AtomId::ROOT);
            out.push(ComposedChild {
                cell: *cell,
                atom,
                role: Role::from_embed(*role),
                placed_by: *placed_by,
                live: true,
            });
        }
    }
    out
}

fn embed_atoms(layout: &LayoutGraph) -> Vec<(AtomId, EmbedRole, ChildCellId, Provenance)> {
    let mut out = Vec::new();
    let mut seen = std::collections::BTreeSet::new();
    let mut stack = vec![AtomId::ROOT];
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        if let Some(a) = layout.atom(id) {
            if let AtomContent::Embed(ChildRef::Cell(cell, _), role) = &a.content {
                out.push((id, *role, *cell, a.provenance));
            }
        }
        for s in layout.successors(id) {
            stack.push(s);
        }
    }
    out.sort_by_key(|(id, _, _, _)| id.0);
    out.dedup_by_key(|(id, _, _, _)| *id);
    out
}

fn is_alive(layout: &LayoutGraph, id: AtomId) -> bool {
    layout.atom(id).map(|a| a.is_alive()).unwrap_or(false)
}

fn last_live_atom(layout: &LayoutGraph) -> AtomId {
    let mut cursor = AtomId::ROOT;
    let mut last = AtomId::ROOT;
    let mut seen = std::collections::BTreeSet::new();
    loop {
        let succ: Vec<AtomId> = layout.successors(cursor).collect();
        let next = match succ.first() {
            Some(n) => *n,
            None => return last,
        };
        if !seen.insert(next) {
            return last;
        }
        if is_alive(layout, next) {
            last = next;
        }
        cursor = next;
    }
}

fn predecessor_of(layout: &LayoutGraph, id: AtomId) -> AtomId {
    let mut seen = std::collections::BTreeSet::new();
    let mut stack = vec![AtomId::ROOT];
    while let Some(cur) = stack.pop() {
        if !seen.insert(cur) {
            continue;
        }
        for s in layout.successors(cur) {
            if s == id {
                return cur;
            }
            stack.push(s);
        }
    }
    AtomId::ROOT
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cell(tag: u128) -> ChildCellId {
        ChildCellId(tag)
    }

    fn doc() -> ComposerCard {
        ComposerCard::open(
            cell(0xD0C),
            Author(7),
            /*held=*/ AuthRequired::None,
            /*edit_authority=*/ AuthRequired::Signature,
        )
    }

    // (a) OPEN — the view is GENERATED from the (empty) composition: a title + the four
    //     gesture buttons + an empty composed section.
    #[test]
    fn open_generates_a_view_with_the_four_gestures() {
        let card = doc();
        let tree = card.view_tree().expect("the generated view parses");
        for g in ["add_embed", "reorder", "remove", "set_role"] {
            assert!(
                tree.has_button_for(g),
                "the composer view carries a `{g}` gesture button"
            );
        }
        assert!(
            tree.walk()
                .iter()
                .any(|n| n.label() == Some("Composed cells")),
            "the composed-children section is labeled"
        );
        assert!(
            tree.walk()
                .iter()
                .any(|n| n.label() == Some("(empty — add an embed)")),
            "an empty composition shows the empty hint"
        );
    }

    // (b) GESTURE — adding two embeds lists them in order; the view regenerates to carry
    //     a row per live child.
    #[test]
    fn add_embeds_appear_as_rows_in_the_regenerated_view() {
        let mut card = doc();
        let intro = cell(0xA1);
        let figure = cell(0xB2);
        let r1 = card.add_embed(intro, Role::Section);
        let r2 = card.add_embed(figure, Role::Figure);
        assert_eq!(r1.author, Author(7));
        assert_ne!(r1.patch, r2.patch, "distinct gestures => distinct receipts");

        let kids = card.children();
        assert_eq!(kids.len(), 2, "both embeds are live children");
        assert_eq!(kids[0].cell, intro);
        assert_eq!(kids[1].cell, figure);
        assert_eq!(kids[0].role, Role::Section);
        assert_eq!(kids[1].role, Role::Figure);

        // The regenerated view carries a row for each child (numbered, with role).
        let tree = card.view_tree().expect("regenerated view parses");
        assert!(
            tree.walk().iter().any(
                |n| matches!(n.label(), Some(l) if l.starts_with("1.") && l.contains("section"))
            ),
            "the first composed child renders as a row with its role"
        );
        assert!(
            tree.walk().iter().any(
                |n| matches!(n.label(), Some(l) if l.starts_with("2.") && l.contains("figure"))
            ),
            "the second composed child renders as a row with its role"
        );
    }

    // (c) REMOVE — a removed child drops off the live rows but is RETAINED + provenanced.
    #[test]
    fn remove_tombstones_not_loses() {
        let mut card = doc();
        let a = cell(0xA1);
        let b = cell(0xB2);
        card.add_embed(a, Role::Section);
        card.add_embed(b, Role::Figure);
        let receipt = card.remove(card.embed_id(a));
        assert_eq!(receipt.author, Author(7));

        let kids = card.children();
        assert_eq!(kids.len(), 1, "the removed child drops off the live render");
        assert_eq!(kids[0].cell, b);

        let roster = card.roster();
        let removed = roster
            .iter()
            .find(|k| k.cell == a)
            .expect("the removed child is retained (tombstoned, not lost)");
        assert!(!removed.live);
        assert_eq!(removed.placed_by, Author(7));
    }

    // (d) SET_ROLE — a child's role reads back changed; the citation is preserved.
    #[test]
    fn set_role_reads_back_and_preserves_citation() {
        let mut card = doc();
        let fig = cell(0xF1);
        card.add_embed(fig, Role::Section);
        assert_eq!(card.children()[0].role, Role::Section);
        let receipt = card
            .set_role(fig, Role::Figure)
            .expect("re-roling a live child succeeds");
        assert_eq!(receipt.author, Author(7));
        let kids = card.children();
        assert_eq!(
            kids.len(),
            1,
            "still one live child (re-roled, not duplicated)"
        );
        assert_eq!(kids[0].role, Role::Figure);
        assert_eq!(kids[0].cell, fig);
        assert!(card.set_role(cell(0xDEAD), Role::Citation).is_none());
    }

    // (e) EDIT FROM WITHIN — relabel a section + append a note: a receipted patch w/ blame.
    #[test]
    fn editing_the_composer_view_from_within_is_a_receipted_patch_with_blame() {
        let mut card = doc();
        card.add_embed(cell(0xA1), Role::Section);
        let source_before = card.view_source();
        let blame_before = card.view_blame().len();

        let edit = card
            .edit_view(ViewPatch::Relabel {
                from: "Composed cells".into(),
                to: "Document body".into(),
            })
            .expect("the authorized relabel reshape is admitted");
        assert_ne!(card.view_source(), source_before, "the view-source changed");
        assert!(
            edit.tree
                .walk()
                .iter()
                .any(|n| n.label() == Some("Document body")),
            "the re-folded view carries the new section label"
        );
        assert!(
            edit.receipt.is_landed(),
            "the structural view-edit left a real composition receipt (a patch on the doc cell)"
        );
        assert_eq!(edit.receipt.author, Author(7));
        assert!(
            card.view_blame().iter().any(|l| l.author == Author(7)),
            "the reshape is blamed on its author"
        );

        let edit2 = card
            .edit_view(ViewPatch::AddText {
                text: "— composed by hand —".into(),
            })
            .expect("the authorized add-text reshape is admitted");
        assert!(
            edit2
                .tree
                .walk()
                .iter()
                .any(|n| n.label() == Some("— composed by hand —")),
            "the appended note landed"
        );
        assert!(
            card.view_blame().len() > blame_before,
            "the reshapes added view-source lines (patches, not a recompile)"
        );
    }

    // (f) the cap tooth — an unauthorized reshape is refused in-band (no patch).
    #[test]
    fn an_unauthorized_reshape_is_refused_in_band() {
        let mut card = ComposerCard::open(
            cell(0xBAD),
            Author(7),
            /*held=*/ AuthRequired::Signature,
            /*edit_authority=*/ AuthRequired::Proof,
        );
        let before = card.view_source();
        let err = card.edit_view(ViewPatch::AddText {
            text: "sneaky".into(),
        });
        assert!(matches!(err, Err(EditError::Unauthorized)));
        assert_eq!(card.view_source(), before, "nothing changed");
    }
}
