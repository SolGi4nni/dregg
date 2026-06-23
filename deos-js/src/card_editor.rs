//! **The card editor** — edit a card (a deos-js applet = a cell) FROM WITHIN deos, each
//! authoring gesture a REAL verified turn / a receipted patch.
//!
//! HYPERDREGGMEDIA gap #1 (`docs/deos/HYPERDREGGMEDIA-NOTES.md` §6): today you can
//! INSPECT + NAVIGATE a card; you cannot EDIT it from within. This module turns
//! inspection into authoring. The unifying truth holds — *every authoring gesture is an
//! affordance; every affordance is a turn; every turn is a receipt* — pointed at a card's
//! own three surfaces:
//!
//!   - **VIEW** ([`CardEditor::edit_view`]) — the keystone. A card's `view_source` IS a
//!     [`ProgramSource`] (a [`dregg_doc::Doc`] patch-history; see [`crate::program_doc`]).
//!     Editing the UI (add a button, change a label) is *appending a patch*: the view
//!     re-folds, re-seals into the card's manifest, and re-renders — and the edit is a
//!     **receipted patch** ([`ProgramSource::blame`] attributes it to its author). The
//!     keystone moment: *edit the UI from within → it re-renders → and the change is an
//!     accountable patch, not a recompile.*
//!   - **FIELD** ([`CardEditor::set_field`]) — a real `SetField` verified turn on the
//!     card's state (a re-read shows the new value; a [`TurnReceipt`] proves it).
//!   - **AFFORDANCE** ([`CardEditor::add_affordance`]) — weld a new named effect-template
//!     into the card's manifest/program. The card now has a new fireable affordance (a
//!     new button), and the weld itself leaves a provenance receipt.
//!
//! THE CAP TOOTH IS KEPT. A [`CardEditor`] is mounted under a `held` authority. Every
//! authoring gesture is bounded by it: `set_field` fires through [`Applet::fire`] (the
//! in-band [`dregg_cell::is_attenuation`] gate), and a view/affordance edit is admitted
//! only when the editor's `held` satisfies the card's *authoring* authority
//! ([`CardEditor::edit_authority`]). An agent driving a `CardEditor` (via
//! `deos-hermes::run_js`) can therefore only author cards it is authorized to — an
//! unauthorized card-edit is refused in-band, no patch, no receipt.
//!
//! THE VIEW SHAPE. A card's view is authored as a **structured view-tree** (the same
//! `{kind, props, children}` JSON `deos-view`'s `parse_view_tree` consumes), so an edit
//! is a structural splice (add a node) the re-fold can be ASSERTED on directly — no
//! SpiderMonkey round-trip needed to prove the new button landed. [`ViewTree`] is the
//! gpui-free mirror; [`CardEditor::view_tree`] is the re-folded shape a renderer paints.

use dregg_cell::state::FieldElement;
use dregg_cell::AuthRequired;
pub use dregg_doc::Author;
use dregg_doc::BlameLine;
use dregg_turn::TurnReceipt;
use serde::{Deserialize, Serialize};

use crate::applet::{pack_u64, Applet, Slot};
use crate::portable::{AffordanceSpec, ApplyOp, AppletManifest, PortableApplet};
use crate::program_doc::ProgramSource;

/// The heap slot the card editor uses to witness an authoring gesture that does not
/// itself mutate a model field (a view-patch or affordance-weld). Bumping it via a real
/// `SetField` turn is how a *structural* authoring edit still leaves a receipt on the
/// cell's chain — "this card's authorship advanced" — alongside the patch/blame record.
pub const AUTHORSHIP_SLOT: Slot = 15;

/// A node of the card's **structured view-tree** — the gpui-free mirror of the
/// `{kind, props, children}` shape `deos-view`'s `parse_view_tree` consumes. Authoring
/// the view edits THIS tree; its JSON is the card's `view_source` (a document).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "lowercase")]
pub enum ViewTree {
    /// A vertical column of children.
    VStack {
        #[serde(default)]
        children: Vec<ViewTree>,
    },
    /// A horizontal row of children.
    Row {
        #[serde(default)]
        children: Vec<ViewTree>,
    },
    /// A static text label.
    Text {
        #[serde(default)]
        props: TextProps,
    },
    /// A live binding to model `slot` (re-read off the ledger by the renderer).
    Bind {
        #[serde(default)]
        props: BindProps,
    },
    /// A button whose click fires affordance `turn` with `arg` (a real verified turn).
    Button {
        #[serde(default)]
        props: ButtonProps,
    },
}

/// `text` props.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct TextProps {
    #[serde(default)]
    pub text: String,
}

/// `bind` props.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct BindProps {
    #[serde(default)]
    pub slot: usize,
    #[serde(default)]
    pub label: String,
}

/// `button` props — its label and the affordance its click fires.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ButtonProps {
    #[serde(default)]
    pub label: String,
    /// Serialized as `on_click` to match `deos-view`'s `parse_view_tree` (the canonical
    /// renderer-side JSON shape it consumes), so a card-editor's re-folded view-source IS
    /// directly renderable.
    #[serde(default, rename = "on_click")]
    pub on_click: OnClick,
}

/// `onClick = { turn, arg }` — the affordance a button fires.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct OnClick {
    #[serde(default)]
    pub turn: String,
    #[serde(default)]
    pub arg: i64,
}

impl ViewTree {
    /// An empty root column (a fresh card's view).
    pub fn root() -> Self {
        ViewTree::VStack { children: vec![] }
    }

    /// Parse a card's `view_source` JSON into a tree.
    pub fn from_json(json: &str) -> Result<Self, String> {
        serde_json::from_str(json).map_err(|e| format!("view-tree JSON: {e}"))
    }

    /// Serialize this tree to its canonical (pretty) JSON — the card's `view_source`.
    /// Pretty so that line-granular patches/blame have line structure to bite on (the
    /// document language is line-granular; see [`ProgramSource`]).
    pub fn to_json(&self) -> String {
        serde_json::to_string_pretty(self).expect("view-tree serializes")
    }

    /// The children of this node (empty for leaves).
    pub fn children(&self) -> &[ViewTree] {
        match self {
            ViewTree::VStack { children } | ViewTree::Row { children } => children,
            _ => &[],
        }
    }

    /// Push a child onto a container node (vstack/row). A no-op on a leaf.
    fn push_child(&mut self, node: ViewTree) {
        match self {
            ViewTree::VStack { children } | ViewTree::Row { children } => children.push(node),
            _ => {}
        }
    }

    /// Walk the whole tree (depth-first), yielding every node.
    pub fn walk(&self) -> Vec<&ViewTree> {
        let mut out = vec![self];
        for c in self.children() {
            out.extend(c.walk());
        }
        out
    }

    /// Does the tree contain a button bound to affordance `turn`? (The assertion the
    /// keystone test makes after a view-patch: the new button is in the re-folded view.)
    pub fn has_button_for(&self, turn: &str) -> bool {
        self.walk().iter().any(|n| {
            matches!(n, ViewTree::Button { props } if props.on_click.turn == turn)
        })
    }

    /// The label of a node, if it has one (for asserting a relabel patch).
    pub fn label(&self) -> Option<&str> {
        match self {
            ViewTree::Text { props } => Some(props.text.as_str()),
            ViewTree::Button { props } => Some(props.label.as_str()),
            _ => None,
        }
    }

    /// Relabel the FIRST text node whose current text equals `from` to `to`. Returns
    /// whether a node was relabelled (so a caller can refuse a no-op edit).
    fn relabel_text(&mut self, from: &str, to: &str) -> bool {
        if let ViewTree::Text { props } = self {
            if props.text == from {
                props.text = to.to_string();
                return true;
            }
        }
        match self {
            ViewTree::VStack { children } | ViewTree::Row { children } => {
                for c in children.iter_mut() {
                    if c.relabel_text(from, to) {
                        return true;
                    }
                }
                false
            }
            _ => false,
        }
    }
}

/// A view-authoring edit — the structural gesture a [`CardEditor::edit_view`] applies to
/// the card's view-tree before re-folding it as a patch.
#[derive(Clone, Debug)]
pub enum ViewPatch {
    /// Append a button (firing `turn` with `arg`) to the root view.
    AddButton {
        label: String,
        turn: String,
        arg: i64,
    },
    /// Append a static text node to the root view.
    AddText { text: String },
    /// Relabel the first text node matching `from` to `to` (change a label).
    Relabel { from: String, to: String },
}

impl ViewPatch {
    /// Apply this gesture to a tree, returning whether it changed anything.
    fn apply(&self, tree: &mut ViewTree) -> bool {
        match self {
            ViewPatch::AddButton { label, turn, arg } => {
                tree.push_child(ViewTree::Button {
                    props: ButtonProps {
                        label: label.clone(),
                        on_click: OnClick {
                            turn: turn.clone(),
                            arg: *arg,
                        },
                    },
                });
                true
            }
            ViewPatch::AddText { text } => {
                tree.push_child(ViewTree::Text {
                    props: TextProps { text: text.clone() },
                });
                true
            }
            ViewPatch::Relabel { from, to } => tree.relabel_text(from, to),
        }
    }
}

/// Why an authoring gesture was refused.
#[derive(Debug)]
pub enum EditError {
    /// The editor's `held` does not satisfy the card's authoring authority — the cap
    /// tooth refused; no patch, no receipt (the bound the agent cannot exceed).
    Unauthorized,
    /// The card's current `view_source` is not a parseable view-tree.
    BadView(String),
    /// The structural edit changed nothing (e.g. a relabel that matched no node).
    NoOp,
    /// The provenance/field turn failed at the executor.
    Fire(String),
}

impl std::fmt::Display for EditError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EditError::Unauthorized => write!(f, "authoring refused by the cap-gate"),
            EditError::BadView(e) => write!(f, "card view is not a parseable view-tree: {e}"),
            EditError::NoOp => write!(f, "the edit changed nothing"),
            EditError::Fire(e) => write!(f, "the authoring provenance turn failed: {e}"),
        }
    }
}
impl std::error::Error for EditError {}

/// The record of a successful view-patch: the re-folded view-tree, the blame (every
/// view line attributed to its authoring patch + author — the keystone "accountable
/// patch, not a recompile"), and the provenance receipt the structural edit left on the
/// card's chain.
pub struct ViewEdit {
    /// The re-folded, re-rendered view-tree (a renderer paints this; the test asserts
    /// the new node is present).
    pub tree: ViewTree,
    /// The blame over the view source — who authored each view line, in which patch.
    pub blame: Vec<BlameLine>,
    /// The receipt of the provenance turn the structural edit left (the cell's
    /// authorship-slot advanced via a real `SetField` turn).
    pub receipt: TurnReceipt,
}

/// **The card editor** — a handle that authors a target card (an [`Applet`]) from
/// within deos, each gesture a verified turn / a receipted patch, all bounded by `held`.
///
/// Construct one over a card with [`CardEditor::adopt`] (lifting the card's current
/// `view_source` into a [`ProgramSource`] document) and the card's *authoring* authority
/// (`edit_authority` — the cap the editor's `held` must satisfy to author it). Then:
/// `edit_view` patches the UI, `set_field` writes a field, `add_affordance` welds a new
/// affordance.
pub struct CardEditor {
    /// The card being authored — its model is the cell state; its affordances fire turns.
    card: Applet,
    /// The card's view source AS A DOCUMENT (a patch-history). Editing the view appends
    /// a patch here; the fold is the card's `view_source`.
    view: ProgramSource,
    /// The card's full manifest (kept in step with the view + affordance edits, so the
    /// card re-seals/re-mints with the authored program).
    manifest: AppletManifest,
    /// The authority the editor holds (what authoring gestures are cap-checked against).
    held: AuthRequired,
    /// The authority a gesture on THIS card requires (the authoring cap tooth). The
    /// editor's `held` must satisfy it ([`dregg_cell::is_attenuation`]).
    edit_authority: AuthRequired,
    /// The author every patch this editor appends is attributed to (the blame identity).
    author: Author,
}

impl CardEditor {
    /// Adopt a card for authoring. `card` is the live applet; `manifest` is its program
    /// (its `view_source` is lifted into a [`ProgramSource`] document authored by
    /// `author`); `held` is the editor's authority and `edit_authority` is the cap a
    /// gesture on this card requires (the editor's `held` must satisfy it).
    pub fn adopt(
        card: Applet,
        manifest: AppletManifest,
        author: Author,
        held: AuthRequired,
        edit_authority: AuthRequired,
    ) -> Self {
        let view = ProgramSource::seed(author, &manifest.view_source);
        CardEditor {
            card,
            view,
            manifest,
            held,
            edit_authority,
            author,
        }
    }

    /// The card being authored (read-only) — for reading its model / receipts.
    pub fn card(&self) -> &Applet {
        &self.card
    }

    /// The card being authored (mutable) — for firing one of its own affordances.
    pub fn card_mut(&mut self) -> &mut Applet {
        &mut self.card
    }

    /// The card's current view source (the document fold).
    pub fn view_source(&self) -> String {
        self.view.view_source()
    }

    /// The card's current manifest (kept in step with the authored program).
    pub fn manifest(&self) -> &AppletManifest {
        &self.manifest
    }

    /// The re-folded view-tree a renderer paints (parsed from the current view source).
    pub fn view_tree(&self) -> Result<ViewTree, EditError> {
        ViewTree::from_json(&self.view.view_source()).map_err(EditError::BadView)
    }

    /// The blame over the card's view source — who authored each view line, in which
    /// patch (the "accountable patch" face).
    pub fn view_blame(&self) -> Vec<BlameLine> {
        self.view.blame()
    }

    /// Whether the editor is authorized to author this card (the authoring cap tooth).
    fn authorized(&self) -> bool {
        dregg_cell::is_attenuation(&self.held, &self.edit_authority)
    }

    /// Fire a real `SetField` provenance turn bumping the card's authorship slot — how a
    /// *structural* authoring gesture (a view-patch / affordance-weld, which does not
    /// itself write a model field) still lands a receipt on the card's chain. Returns the
    /// receipt. (Registered as an internal affordance the first time it is needed.)
    fn provenance_turn(&mut self) -> Result<TurnReceipt, EditError> {
        let next = self.card.model().field_u64(AUTHORSHIP_SLOT) + 1;
        // Register the provenance affordance lazily (idempotent — re-registering replaces
        // an identical entry). It is gated on the SAME edit_authority the cap tooth
        // already cleared above, so it can only fire when authoring is authorized.
        self.card.register_affordance(crate::applet::Affordance {
            name: "__authorship__".into(),
            required: self.edit_authority.clone(),
            apply: Box::new(move |_model, _arg| vec![(AUTHORSHIP_SLOT, pack_u64(next))]),
        });
        self.card
            .fire("__authorship__", 0)
            .map_err(|e| EditError::Fire(e.to_string()))
    }

    /// **EDIT THE VIEW — the keystone.** Apply a structural view gesture (add a button,
    /// add text, relabel) to the card's view-tree, append the result as a PATCH to the
    /// card's `view_source` document, re-seal the fold into the manifest, and leave a
    /// provenance receipt on the card's chain.
    ///
    /// The result is the re-folded view-tree (a renderer re-paints it — the test asserts
    /// the new node is present), the blame (each view line attributed — the edit is an
    /// *accountable patch, not a recompile*), and the provenance receipt.
    ///
    /// Refused in-band if the editor's `held` does not satisfy the card's
    /// `edit_authority` (the cap tooth — an agent can only author cards it may author) or
    /// if the gesture changed nothing.
    pub fn edit_view(&mut self, patch: ViewPatch) -> Result<ViewEdit, EditError> {
        if !self.authorized() {
            return Err(EditError::Unauthorized);
        }

        // Apply the structural gesture to the current view-tree.
        let mut tree = self.view_tree()?;
        if !patch.apply(&mut tree) {
            return Err(EditError::NoOp);
        }
        let new_source = tree.to_json();

        // PATCH — the edit is appended to the view document (NOT a wholesale rewrite),
        // so blame attributes the new lines to this editor's author.
        self.view.edit(self.author, &new_source);

        // Re-seal the fold into the manifest so the card re-mints/re-renders with the
        // authored view (the document is the source of truth; the fold is what runs).
        self.manifest.view_source = self.view.view_source();

        // Leave a provenance receipt on the card's chain (a structural edit still lands
        // a verified turn — the cell's authorship advanced).
        let receipt = self.provenance_turn()?;

        let tree = self.view_tree()?;
        Ok(ViewEdit {
            tree,
            blame: self.view.blame(),
            receipt,
        })
    }

    /// **EDIT A FIELD** — set model `slot` to `value` as a real `SetField` verified turn
    /// on the card's state. A re-read ([`Applet::get_u64`]) reflects the new value; the
    /// returned [`TurnReceipt`] proves it. Bounded by the editor's `held` (the in-band
    /// cap tooth in [`Applet::fire`]).
    pub fn set_field(&mut self, slot: Slot, value: u64) -> Result<TurnReceipt, EditError> {
        if !self.authorized() {
            return Err(EditError::Unauthorized);
        }
        // Register a one-shot SET affordance for this slot/value, gated on edit_authority,
        // then fire it — a real verified turn whose write is `slot := value`.
        let v = value;
        let s = slot;
        self.card.register_affordance(crate::applet::Affordance {
            name: "__set_field__".into(),
            required: self.edit_authority.clone(),
            apply: Box::new(move |_model, _arg| vec![(s, pack_u64(v))]),
        });
        self.card
            .fire("__set_field__", 0)
            .map_err(|e| EditError::Fire(e.to_string()))
    }

    /// **ADD AN AFFORDANCE** — weld a new named effect-template into the card's
    /// manifest/program. The card gains a new fireable affordance (and a renderer can add
    /// the button for it). The weld is registered live on the card (so it fires
    /// immediately) AND recorded in the manifest (so it travels with the cell), and leaves
    /// a provenance receipt. Bounded by the editor's `held`.
    pub fn add_affordance(&mut self, spec: AffordanceSpec) -> Result<TurnReceipt, EditError> {
        if !self.authorized() {
            return Err(EditError::Unauthorized);
        }
        // Record in the manifest (travels with the cell when re-minted).
        self.manifest
            .affordances
            .retain(|a| a.name != spec.name);
        self.manifest.affordances.push(spec.clone());
        // Register live on the card so the new affordance fires NOW.
        self.card.register_affordance(crate::applet::Affordance {
            name: spec.name.clone(),
            required: spec.required.clone(),
            apply: spec.op.into_closure(),
        });
        // Leave a provenance receipt (the program advanced).
        self.provenance_turn()
    }

    /// Re-mint the authored card as a fresh portable cell-blob — the authored program
    /// (the patched view + the welded affordances + the current model seed) sealed into a
    /// new cell. The handoff path: an edited card carried over the membrane carries its
    /// authored program in its committed heap.
    pub fn reseal(&self) -> AppletManifest {
        self.manifest.clone()
    }

    /// Re-mint the authored manifest into a fresh portable applet (the authored card,
    /// reconstituted — its view patched, its affordances welded). Proves the authored
    /// program is a real, runnable, portable cell.
    pub fn remint(&self, public_key: [u8; 32], token_id: [u8; 32]) -> Applet {
        PortableApplet::mint(public_key, token_id, &self.manifest)
    }
}

/// A convenience: the declarative apply rule a welded affordance carries (re-exported so
/// a card-editor caller need not reach into `portable`). The new button's turn.
pub type WeldOp = ApplyOp;

/// Pack a field element for a card field (re-exported convenience).
pub fn field_value(v: u64) -> FieldElement {
    pack_u64(v)
}
