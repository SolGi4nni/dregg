//! **THE DYNAMICS-FEED CARD** — the cockpit's live dynamics feed, reborn as a deos-js card.
//!
//! Today the cockpit's dynamics feed (the scrolling stream of recent turns/receipts — see
//! `starbridge-v2/src/dynamics.rs`) is hardcoded Rust gpui: its UI is *compiled code*, so
//! you cannot reshape it without a rebuild and the agent cannot rewrite it. This module
//! makes the feed a **deos-js card** — a cell whose view is a *view-tree*
//! ([`crate::card_editor::ViewTree`], the same `{kind, props, children}` shape [`deos-view`]
//! renders) generated from the live stream of committed turns:
//!
//!   - a **header** ([`ViewTree::Text`]) naming the feed + how many entries it shows;
//!   - a **live entry-count** ([`ViewTree::Bind`]) bound to the card's `FEED_LEN_SLOT`, so a
//!     new turn that appends an entry advances the displayed count in place (the renderer
//!     re-reads it off the live ledger — a landed turn updates the row without a re-fold);
//!   - one **entry row** ([`ViewTree::Text`]) per recent transition, most-recent-LAST, each
//!     a legible `@h<height> · <effect-kind> · <author>` line (height, effect-kind, author —
//!     the same triple `WorldEvent` carries).
//!
//! ## The feed APPENDS on a new turn
//!
//! [`DynamicsCard::observe`] is how a new turn enters the feed: it pushes a [`FeedEntry`]
//! (height + effect-kind + author), fires a real `SetField` turn that bumps the card's
//! `FEED_LEN_SLOT` (so the bound entry-count row advances — the live binding the renderer
//! re-reads), and re-derives the entry rows. The card thus "scrolls" as the world commits
//! turns: each observed transition is one more row, the newest at the bottom, the bound
//! length tracking the stream.
//!
//! ## Editable from within
//!
//! Because the view is *data* (a view-tree = the card's `view_source` document), it is
//! **editable from within**: [`DynamicsCard::edit_view`] patches the feed card's OWN
//! view-source — relabel the header, append a filter button — as a *receipted patch* with
//! *blame*. The feed UI reshapes live; the edit is an accountable patch, not a recompile.
//!
//! ## The cap tooth is kept
//!
//! Both teeth are the proven [`dregg_cell::is_attenuation`] gate: an observe (which bumps a
//! field via a real turn) and a view-edit are admitted only when `held` satisfies the card's
//! `edit_authority` ([`DynamicsCard::authorized`]). An unauthorized reshape is refused
//! in-band — no patch, no receipt.

use dregg_cell::AuthRequired;
use dregg_doc::{Author, BlameLine};
use dregg_turn::TurnReceipt;

use deos_reflect::short_hex;

use crate::applet::{pack_u64, Affordance, Applet, Slot};
use crate::card_editor::{
    BindProps, ButtonProps, EditError, OnClick, TextProps, ViewEdit, ViewPatch, ViewTree,
};
use crate::program_doc::ProgramSource;
use dregg_cell::Requirement;

/// The model slot whose value is the live feed length — the [`ViewTree::Bind`] the renderer
/// re-reads, advanced by a real `SetField` turn each time a new entry is observed. Disjoint
/// from the inspector/card-editor authorship slots.
pub const FEED_LEN_SLOT: Slot = 12;

/// How many recent entries the feed renders as rows (most-recent-LAST). The bound length row
/// shows the TOTAL count; the rows show this tail.
const DEFAULT_TAIL: usize = 16;

/// One observed state transition in the feed — the gpui-free mirror of the `(height,
/// effect-kind, author)` triple `starbridge-v2::dynamics::WorldEvent` carries. A feed row is
/// a pure function of this, so the card's rows are `cargo test`-able without a World.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FeedEntry {
    /// The chain height the turn committed at (the feed's temporal/causal index).
    pub height: u64,
    /// The effect-kind label (e.g. "turn committed", "balance flowed", "cap granted") — the
    /// human-meaningful kind of transition, the same labels `WorldEvent::label` produces.
    pub effect_kind: String,
    /// The author of the turn (a short legible cell id) — who committed it.
    pub author: String,
}

impl FeedEntry {
    /// Build an entry from a height, an effect-kind label, and the author's raw cell bytes
    /// (rendered short). The single constructor the cockpit's `WorldEvent` adapter calls.
    pub fn new(height: u64, effect_kind: impl Into<String>, author: &[u8; 32]) -> Self {
        FeedEntry {
            height,
            effect_kind: effect_kind.into(),
            author: short_hex(author),
        }
    }

    /// The legible feed-row line: `@h<height> · <effect-kind> · <author>`.
    pub fn row_text(&self) -> String {
        format!("@h{} · {} · {}", self.height, self.effect_kind, self.author)
    }
}

/// **The dynamics-feed card** — a deos-js card whose view is a view-tree generated from a
/// live stream of recent turns/receipts, rendered over a live World, bound so a new turn
/// appends a row, and editable from within (each edit a receipted patch with blame).
pub struct DynamicsCard {
    /// The card's substance — a cell on a live embedded verified World. A new-entry observe
    /// fires a real `SetField` turn on it (bumping [`FEED_LEN_SLOT`]); its own view-source is
    /// the thing edit-from-within rewrites.
    card: Applet,
    /// The feed's observed entries, in arrival order (most-recent-LAST). The rows are derived
    /// from the tail of this; the bound length row shows its full count.
    entries: Vec<FeedEntry>,
    /// The card's view-source AS A DOCUMENT (a patch-history). Regenerated as the feed grows;
    /// every edit-from-within appends a patch, so [`Self::view_blame`] attributes each line.
    view: ProgramSource,
    /// The authority the card's driver holds (the cap an observe + a view-edit are checked
    /// against).
    held: AuthRequired,
    /// The authority a reshape/observe on THIS card requires (`held` must satisfy it).
    edit_authority: Requirement,
    /// The author every view-patch is attributed to (the blame identity).
    author: Author,
}

impl DynamicsCard {
    /// **Open the feed card** over a live substance cell. The initial view-tree is GENERATED
    /// from the current (possibly empty) entry stream and seeded as the card's editable
    /// `view_source` document — so the feed is a data-defined card from birth.
    pub fn open(
        card: Applet,
        author: Author,
        held: AuthRequired,
        edit_authority: Requirement,
    ) -> Self {
        let entries: Vec<FeedEntry> = Vec::new();
        let initial = feed_view(&entries).to_json();
        let view = ProgramSource::seed(author, &initial);
        DynamicsCard {
            card,
            entries,
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
    /// (the `Bind` length row re-reads its model). The card's current `view_source` is the
    /// view-tree the renderer paints over it.
    pub fn into_card(self) -> Applet {
        self.card
    }

    /// The card's current view source (the document fold) — the `view_source` a renderer
    /// parses into a [`deos_view::ViewNode`] tree and paints.
    pub fn view_source(&self) -> String {
        self.view.view_source()
    }

    /// The card's view-tree (the re-folded shape a renderer paints), parsed from the current
    /// view source.
    pub fn view_tree(&self) -> Result<ViewTree, EditError> {
        ViewTree::from_json(&self.view.view_source()).map_err(EditError::BadView)
    }

    /// The blame over the card's view source — who authored each view line, in which patch.
    pub fn view_blame(&self) -> Vec<BlameLine> {
        self.view.blame()
    }

    /// The feed's observed entries (read-only) — the stream the rows are derived from.
    pub fn entries(&self) -> &[FeedEntry] {
        &self.entries
    }

    /// The live entry count (the value the bound length row shows) — read off the live ledger
    /// (so a test can assert an observe advanced it).
    pub fn live_len(&self) -> u64 {
        self.card.get_u64(FEED_LEN_SLOT)
    }

    /// Whether the card is authorized to advance / reshape itself (the cap tooth).
    fn authorized(&self) -> bool {
        self.edit_authority.satisfied_by(&self.held)
    }

    /// Fire a real `SetField` turn setting the card's [`FEED_LEN_SLOT`] to the current entry
    /// count — how a new observed entry advances the bound length row (a real verified turn,
    /// gated on the same `edit_authority` the cap tooth clears). Returns the receipt.
    fn bump_len_turn(&mut self) -> Result<TurnReceipt, EditError> {
        let len = self.entries.len() as u64;
        self.card.register_affordance(Affordance {
            name: "__feed_len__".into(),
            required: self.edit_authority.clone(),
            apply: Box::new(move |_model, _arg| vec![(FEED_LEN_SLOT, pack_u64(len))]),
        });
        self.card
            .fire("__feed_len__", 0)
            .map_err(|e| EditError::Fire(e.to_string()))
    }

    /// **OBSERVE A NEW TURN — the feed appends.** Push `entry` onto the stream (most-recent-
    /// LAST), fire a real `SetField` turn advancing the bound length row (so the displayed
    /// count tracks the stream), and re-derive the entry rows as a fresh patch on the
    /// view-source document. Returns the receipt of the length-bump turn.
    ///
    /// Refused in-band if `held` does not satisfy the card's `edit_authority` (the cap tooth)
    /// — no entry, no patch, no receipt.
    pub fn observe(&mut self, entry: FeedEntry) -> Result<TurnReceipt, EditError> {
        if !self.authorized() {
            return Err(EditError::Unauthorized);
        }
        self.entries.push(entry);
        // The bound length row advances via a real verified turn (the displayed count).
        let receipt = self.bump_len_turn()?;
        // Re-derive the rows as a fresh patch (the newest entry is the bottom row).
        let fresh = feed_view(&self.entries).to_json();
        self.view.edit(self.author, &fresh);
        Ok(receipt)
    }

    /// **EDIT THE VIEW FROM WITHIN.** Apply a structural reshape (relabel the header, append
    /// a filter button) to the feed card's OWN view-tree, append the result as a PATCH to the
    /// card's `view_source` document, and leave a provenance receipt on the card's chain.
    ///
    /// The result is the re-folded view-tree (a renderer re-paints it — the feed UI reshapes
    /// live), the blame (each view line attributed), and the provenance receipt. Refused
    /// in-band if `held` does not satisfy `edit_authority`, or if the reshape changed nothing.
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
        let receipt = self.bump_len_turn()?;
        let tree = self.view_tree()?;
        Ok(ViewEdit {
            tree,
            blame: self.view.blame(),
            receipt,
        })
    }
}

/// **Generate the dynamics-feed view-tree** from a stream of observed entries: a header, a
/// live-bound total-length row, and one row per recent entry (most-recent-LAST). Pure (a
/// function of the entry stream), so the rows are `cargo test`-able without a World.
pub fn feed_view(entries: &[FeedEntry]) -> ViewTree {
    let mut children: Vec<ViewTree> = Vec::new();

    // Header.
    children.push(ViewTree::Text {
        props: TextProps {
            text: "Dynamics".into(),
        },
    });

    // The live entry-count — a `Bind` the renderer re-reads off FEED_LEN_SLOT, so a new
    // observed turn (which bumps that slot) advances the displayed count in place.
    children.push(ViewTree::Bind {
        props: BindProps {
            slot: FEED_LEN_SLOT,
            label: "turns observed: ".into(),
        },
    });

    // The recent entry rows (most-recent-LAST), one Text per transition.
    let start = entries.len().saturating_sub(DEFAULT_TAIL);
    let mut rows: Vec<ViewTree> = vec![ViewTree::Text {
        props: TextProps {
            text: "recent turns".into(),
        },
    }];
    if entries.is_empty() {
        rows.push(ViewTree::Text {
            props: TextProps {
                text: "(no turns observed yet)".into(),
            },
        });
    } else {
        for entry in &entries[start..] {
            rows.push(ViewTree::Text {
                props: TextProps {
                    text: entry.row_text(),
                },
            });
        }
    }
    children.push(ViewTree::VStack { children: rows });

    ViewTree::VStack { children }
}

/// Apply a [`ViewPatch`] reshape to a view-tree (append a button/text to the root, or relabel
/// the first matching text). Mirrors the inspector card's apply (the `ViewPatch::apply` is
/// private to `card_editor`).
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

/// Push a child onto a container node (vstack/row). Returns whether it landed (false on a leaf).
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
