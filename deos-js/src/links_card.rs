//! **THE WHAT-LINKS-HERE CARD** — the cockpit's two-way-link panel, reborn as a deos-js card.
//!
//! Ted Nelson's grievance with the web was the **one-way link**: a forward link points OUT;
//! nothing points back, so "what links here" is unanswerable except by a crawler's guess. The
//! cockpit's what-links-here panel (see `starbridge-v2/src/links_here.rs`) renders the link
//! the OTHER way — *who transcludes / observes ME* — over the genuine [`Backlinks`]
//! witness-graph. But that panel is hardcoded Rust gpui: you cannot reshape it without a
//! rebuild and the agent cannot rewrite it. This module makes it a **deos-js card** — a cell
//! whose view is a *view-tree* ([`crate::card_editor::ViewTree`], the `{kind, props,
//! children}` shape [`deos-view`] renders) generated from the focused cell's verified
//! backlinks:
//!
//!   - a **header** ([`ViewTree::Text`]) naming the question + the focused cell's `dregg://`
//!     identity, and the viewer tier the graph is projected FOR (the link fog-of-war);
//!   - a **visible-of-total** row — how many backlinks the viewer sees of how many the
//!     god's-eye docuverse holds (so an omission is legible);
//!   - one **backlink row** ([`ViewTree::Text`]) per observer the viewer is cleared to see,
//!     each a verifiable fact `← <observer> transcludes <focus> · receipt <hash> · commitment
//!     <hash>` — never a dangling pointer.
//!
//! ## Everything here is the REAL witness-graph
//!
//! The graph is built by resolving GENUINE transclusions among the cells: each cell is
//! published as a `dregg://` page into one [`WebOfCells`], and each cell transcludes the NEXT
//! cell's finalized field through the real [`TranscludedField::include`] (content → commitment
//! → receipt → quorum) — a ring. Each resolved quote is recorded into a real [`Backlinks`] via
//! [`Backlinks::observe`], so the backlink of cell *N* is cell *N−1*, a verifiable fact, not a
//! fabricated edge. A forged or non-finalized quote could not be `include`d, so it could not be
//! recorded.
//!
//! ## Editable from within
//!
//! Because the view is *data*, it is **editable from within**: [`LinksCard::edit_view`]
//! patches the panel's OWN view-source — relabel the header, append a navigate button — as a
//! *receipted patch* with *blame*. The panel UI reshapes live; the edit is an accountable
//! patch, not a recompile. The cap tooth (the proven [`dregg_cell::is_attenuation`] gate)
//! refuses an unauthorized reshape in-band — no patch, no receipt.

use dregg_cell::{AuthRequired, CellId};
use dregg_doc::{Author, BlameLine};
use dregg_turn::TurnReceipt;

use deos_reflect::short_hex;
use starbridge_web_surface::transclusion::{Backlinks, TranscludedField};
use starbridge_web_surface::web_of_cells::{DreggUri, WebOfCells};

use crate::applet::{pack_u64, Affordance, Applet, Slot};
use crate::card_editor::{
    BindProps, ButtonProps, EditError, OnClick, TextProps, ViewEdit, ViewPatch, ViewTree,
};
use crate::program_doc::ProgramSource;
use dregg_cell::Requirement;

/// The model slot whose value is the count of backlinks the viewer sees — the
/// [`ViewTree::Bind`] the renderer re-reads, advanced by a real `SetField` turn when the
/// panel is (re)built. Disjoint from the inspector/feed/agent/card-editor slots.
pub const LINK_COUNT_SLOT: Slot = 11;

/// One **backlink row** the panel renders — a verifiable two-way link: who transcludes the
/// focus, with the cited receipt + content commitment of the observation. The gpui-free
/// mirror of `starbridge-v2::links_here::BacklinkRow`, read off a real [`Backlinks`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BacklinkRow {
    /// The `dregg://<hex>` address of the cell that observes/transcludes the focus (the
    /// navigable end — "what links here points back FROM").
    pub observer_uri: String,
    /// The cited RECEIPT the observation was pinned to (short-hex) — the immutable past that
    /// dates the backlink, making it a verifiable fact, not a bare pointer.
    pub receipt_hash: String,
    /// The source content commitment that was observed (short-hex) — what value was quoted.
    pub content_hash: String,
}

impl BacklinkRow {
    /// The legible backlink-row line.
    pub fn row_text(&self, focus_short: &str) -> String {
        format!(
            "← {} transcludes dregg://{} · receipt {} · commitment {}",
            self.observer_uri, focus_short, self.receipt_hash, self.content_hash
        )
    }
}

/// **The what-links-here card** — a deos-js card whose view is a view-tree generated from a
/// focused cell's verified backlinks (the real witness-graph), projected per-viewer, and
/// editable from within (each edit a receipted patch with blame).
pub struct LinksCard {
    /// The card's substance — a cell on a live embedded verified World. A view-edit (and the
    /// link-count bump) leaves a real `SetField` turn on it; its own view-source is what
    /// edit-from-within rewrites.
    card: Applet,
    /// The focused cell the question "what links here?" is asked OF.
    focus: CellId,
    /// The focused cell's backlinks the viewer is cleared to see (the real, cited rows).
    backlinks: Vec<BacklinkRow>,
    /// How many backlinks the GOD'S-EYE (unprojected) graph holds for the focus — the total
    /// the docuverse has, so a per-viewer omission (`backlinks.len() ≤ total`) is legible.
    total: usize,
    /// The card's view-source AS A DOCUMENT (a patch-history). Every edit-from-within appends
    /// a patch, so [`Self::view_blame`] attributes each line.
    view: ProgramSource,
    /// The authority the card's driver holds (the cap a view-edit is checked against).
    held: AuthRequired,
    /// The authority a reshape on THIS card requires (`held` must satisfy it).
    edit_authority: Requirement,
    /// The author every view-patch is attributed to (the blame identity).
    author: Author,
}

impl LinksCard {
    /// **Open the what-links-here card** for `focus`, answering it over a witness-graph built
    /// from `cells` (each published as a `dregg://` page, each transcluding the next — a ring).
    /// `viewer` is the authority the backlinks are projected FOR. The initial view-tree is
    /// GENERATED from the focused cell's verified backlinks and seeded as the card's editable
    /// `view_source`.
    pub fn open(
        card: Applet,
        focus: CellId,
        cells: &[CellId],
        viewer: AuthRequired,
        author: Author,
        held: AuthRequired,
        edit_authority: Requirement,
    ) -> Self {
        let (backlinks, total) = build_backlinks(focus, cells, &viewer);
        let initial = links_view(focus, &viewer, &backlinks, total).to_json();
        let view = ProgramSource::seed(author, &initial);
        LinksCard {
            card,
            focus,
            backlinks,
            total,
            view,
            held,
            edit_authority,
            author,
        }
    }

    /// The card's substance cell (read-only).
    pub fn card(&self) -> &Applet {
        &self.card
    }

    /// Consume the card, yielding its substance [`Applet`] — the live cell a renderer drives
    /// (the `Bind` link-count row re-reads its model).
    pub fn into_card(self) -> Applet {
        self.card
    }

    /// The focused cell the panel is rooted at.
    pub fn focus(&self) -> CellId {
        self.focus
    }

    /// The card's current view source (the document fold).
    pub fn view_source(&self) -> String {
        self.view.view_source()
    }

    /// The card's view-tree (the re-folded shape a renderer paints).
    pub fn view_tree(&self) -> Result<ViewTree, EditError> {
        ViewTree::from_json(&self.view.view_source()).map_err(EditError::BadView)
    }

    /// The blame over the card's view source — who authored each view line, in which patch.
    pub fn view_blame(&self) -> Vec<BlameLine> {
        self.view.blame()
    }

    /// The focused cell's backlinks the viewer is cleared to see (read-only, the cited rows).
    pub fn backlinks(&self) -> &[BacklinkRow] {
        &self.backlinks
    }

    /// How many backlinks the GOD'S-EYE docuverse holds for the focus (the total — so an
    /// omission is legible: `backlinks().len() ≤ total()`).
    pub fn total(&self) -> usize {
        self.total
    }

    /// How many backlinks the viewer's tier FOGGED away (god's-eye total minus what it sees).
    pub fn fogged_count(&self) -> usize {
        self.total.saturating_sub(self.backlinks.len())
    }

    /// Is the focused cell transcluded by NOBODY the viewer can see? (An honest empty readout.)
    pub fn is_empty(&self) -> bool {
        self.backlinks.is_empty()
    }

    /// The live visible-backlink count (the value the bound count row shows) — read off the
    /// live ledger (so a test can assert the panel build advanced it).
    pub fn live_count(&self) -> u64 {
        self.card.get_u64(LINK_COUNT_SLOT)
    }

    /// Whether the card is authorized to advance / reshape itself (the cap tooth).
    fn authorized(&self) -> bool {
        self.edit_authority.satisfied_by(&self.held)
    }

    /// Fire a real `SetField` turn setting the card's [`LINK_COUNT_SLOT`] to the count of
    /// visible backlinks — the bound count row, advanced by a real verified turn (gated on
    /// `edit_authority`). Returns the receipt.
    fn bump_count_turn(&mut self) -> Result<TurnReceipt, EditError> {
        let count = self.backlinks.len() as u64;
        self.card.register_affordance(Affordance {
            name: "__link_count__".into(),
            required: self.edit_authority.clone(),
            apply: Box::new(move |_model, _arg| vec![(LINK_COUNT_SLOT, pack_u64(count))]),
        });
        self.card
            .fire("__link_count__", 0)
            .map_err(|e| EditError::Fire(e.to_string()))
    }

    /// **PUBLISH THE LIVE COUNT** — fire the bound-count turn so the displayed visible-backlink
    /// count reflects the panel's current rows. Returns the receipt (a real verified turn on
    /// the card's chain). Refused in-band on an unauthorized card (the cap tooth).
    pub fn publish_count(&mut self) -> Result<TurnReceipt, EditError> {
        if !self.authorized() {
            return Err(EditError::Unauthorized);
        }
        self.bump_count_turn()
    }

    /// **EDIT THE VIEW FROM WITHIN.** Apply a structural reshape (relabel the header, append a
    /// navigate button) to the panel's OWN view-tree, append the result as a PATCH to the
    /// view-source document, and leave a provenance receipt on the card's chain. Refused
    /// in-band on an unauthorized reshape (the cap tooth) or a no-op.
    pub fn edit_view(&mut self, patch: ViewPatch) -> Result<ViewEdit, EditError> {
        if !self.authorized() {
            return Err(EditError::Unauthorized);
        }
        let mut tree = self.view_tree()?;
        if !apply_patch(&patch, &mut tree) {
            return Err(EditError::NoOp);
        }
        let new_source = tree.to_json();
        self.view.edit(self.author, &new_source);
        let receipt = self.bump_count_turn()?;
        let tree = self.view_tree()?;
        Ok(ViewEdit {
            tree,
            blame: self.view.blame(),
            receipt,
        })
    }
}

/// Build the focused cell's backlinks (and the god's-eye total) from a REAL [`Backlinks`]
/// witness-graph over `cells`: publish each cell as a `dregg://` page into one
/// [`WebOfCells`], resolve a genuine [`TranscludedField::include`] of the NEXT cell from each
/// (a ring), and record each into the graph. Returns the focus's verified backlink rows the
/// `viewer` is cleared to see, and the total the god's-eye graph holds.
///
/// The per-viewer projection: a focus's backlinks are GATED behind a `Proof` link lineage —
/// the fog-of-war. A viewer whose tier cannot meet that lineage ([`dregg_cell::is_attenuation`]
/// of the viewer against `Proof`) sees the focus's backlinks OMITTED; the total still records
/// what the god's-eye graph holds, so the omission is legible.
pub fn build_backlinks(
    focus: CellId,
    cells: &[CellId],
    viewer: &AuthRequired,
) -> (Vec<BacklinkRow>, usize) {
    let mut web = WebOfCells::new(3);

    // Publish every cell as its own dregg:// page (stable per-cell seeds → deterministic
    // navigable addresses). `page_of` maps a cell to its published page cell (the node the
    // graph keys on), `uri_of` to its navigable `dregg://` URI.
    let mut page_of: std::collections::BTreeMap<CellId, CellId> = std::collections::BTreeMap::new();
    let mut uri_of: std::collections::BTreeMap<CellId, DreggUri> =
        std::collections::BTreeMap::new();
    for (i, cell) in cells.iter().enumerate() {
        let body = page_body_for_cell(cell);
        let url = format!("dregg://cell/{}", short_hex(cell.as_bytes()));
        let uri = web.publish(i as u8, body.as_bytes(), &url);
        page_of.insert(*cell, uri.cell);
        uri_of.insert(*cell, uri);
    }

    // The ring of REAL transclusions: cell N transcludes cell N+1's finalized field. Recorded
    // the OTHER way, this is the backlink "page(N+1) ← page(N)". `observe` keys by the source
    // page the quote points at (the published page cell).
    let mut links = Backlinks::new();
    if cells.len() >= 2 {
        for i in 0..cells.len() {
            let observer = cells[i];
            let source = cells[(i + 1) % cells.len()];
            let source_uri = uri_of.get(&source).expect("source published");
            let observer_page = *page_of.get(&observer).expect("observer published");
            if let Ok(field) = TranscludedField::include(&web, source_uri) {
                links.observe(observer_page, &field);
            }
        }
    }

    // The focus's page (the node the question is asked of). No page → an honest empty readout.
    let Some(focus_page) = page_of.get(&focus).copied() else {
        return (Vec::new(), 0);
    };

    // The god's-eye backlink set for the focus (every observer in the graph, no fog).
    let observers = links.observers_of(focus_page);
    let total = observers.len();

    // THE FOG-OF-WAR: the focus's backlinks are gated behind a `Proof` link lineage. A viewer
    // whose tier can meet `Proof` (None=root, Proof, Either) projects them; an incomparable
    // viewer (Signature) cannot, so they are OMITTED. The total still records the god's-eye
    // count, so the omission is legible.
    let viewer_clears = dregg_cell::is_attenuation(viewer, &AuthRequired::Proof);
    let rows = if viewer_clears {
        observers
            .iter()
            .map(|o| BacklinkRow {
                observer_uri: format!("dregg://{}", short_hex(o.observer.as_bytes())),
                receipt_hash: short_hex(&o.receipt_hash),
                content_hash: short_hex(&o.content_hash),
            })
            .collect()
    } else {
        Vec::new()
    };

    (rows, total)
}

/// **Generate the what-links-here view-tree** from the focused cell's verified backlinks: a
/// header (the question + the focus's `dregg://` identity + the viewer tier), a live-bound
/// visible-count row, a visible-of-total row, and one row per backlink the viewer sees. Pure,
/// so the rows are `cargo test`-able.
pub fn links_view(
    focus: CellId,
    viewer: &AuthRequired,
    backlinks: &[BacklinkRow],
    total: usize,
) -> ViewTree {
    let focus_short = short_hex(focus.as_bytes());
    let mut children: Vec<ViewTree> = Vec::new();

    // Header.
    children.push(ViewTree::Text {
        props: TextProps {
            text: "What Links Here".into(),
        },
    });
    children.push(ViewTree::Text {
        props: TextProps {
            text: format!("dregg://{focus_short} (focus) · viewer {viewer:?}"),
        },
    });

    // The live visible-backlink count — a `Bind` the renderer re-reads off LINK_COUNT_SLOT.
    children.push(ViewTree::Bind {
        props: BindProps {
            slot: LINK_COUNT_SLOT,
            label: "backlinks visible: ".into(),
        },
    });

    // The visible-of-total (the fog made legible).
    let fogged = total.saturating_sub(backlinks.len());
    children.push(ViewTree::Text {
        props: TextProps {
            text: format!(
                "you see {} of {} backlink(s) — {} fogged by your tier",
                backlinks.len(),
                total,
                fogged
            ),
        },
    });

    // The backlink rows (each a verifiable, cited fact).
    let mut rows: Vec<ViewTree> = vec![ViewTree::Text {
        props: TextProps {
            text: "Backlinks".into(),
        },
    }];
    if backlinks.is_empty() {
        rows.push(ViewTree::Text {
            props: TextProps {
                text: "no backlinks visible to you — nobody you are cleared to see transcludes this cell"
                    .into(),
            },
        });
    } else {
        for b in backlinks {
            rows.push(ViewTree::Text {
                props: TextProps {
                    text: b.row_text(&focus_short),
                },
            });
        }
    }
    children.push(ViewTree::VStack { children: rows });

    ViewTree::VStack { children }
}

/// The page body a `dregg://` cell serves (the attested content the receipt + quorum bind) —
/// a real, human-readable description keyed on the cell id (mirrors the cockpit's panel).
fn page_body_for_cell(cell: &CellId) -> String {
    format!(
        "<dregg-cell id=\"{}\"><p>A live capability-secured cell in the verified image. \
         Every interaction with it is a verified turn; this page is served from its \
         committed state.</p></dregg-cell>",
        short_hex(cell.as_bytes())
    )
}

/// Apply a [`ViewPatch`] reshape to a view-tree (append a button/text to the root, or relabel
/// the first matching text). Mirrors the inspector card's apply.
fn apply_patch(patch: &ViewPatch, tree: &mut ViewTree) -> bool {
    match patch {
        ViewPatch::AddButton { label, turn, arg } => push_child(
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
        ),
        ViewPatch::AddText { text } => push_child(
            tree,
            ViewTree::Text {
                props: TextProps { text: text.clone() },
            },
        ),
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
