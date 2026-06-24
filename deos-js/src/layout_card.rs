//! **THE LAYOUT CARD** — the cockpit's own STRUCTURE (its mode→surface arrangement),
//! reborn as a deos-js card. Rung 3 of the reflective cockpit.
//!
//! Rungs 1+2 made the cockpit's *surfaces* deos-js cards (the inspector + 6 mounted, each
//! edit-from-within). This module makes the cockpit's *layout itself* a card: today the
//! arrangement — which surfaces live in which of the five modes
//! (Inhabit/Author/Dev/Inspect/Operate), in what order — is hardcoded Rust gpui
//! (`starbridge-v2/src/cockpit/frame.rs` `CockpitMode::surfaces()`): *compiled code*, so you
//! cannot move a surface to another mode, add one, or reorder without a rebuild, and the
//! agent cannot reshape the chrome. This module makes that arrangement editable DATA — a
//! cell whose state is the mode→surfaces mapping, rendered as a *view-tree*
//! ([`crate::card_editor::ViewTree`], the same `{kind, props, children}` shape [`deos-view`]
//! renders):
//!
//!   - the **layout model** ([`LayoutModel`]) — an ordered list of the five modes, each with
//!     its blurb and its ordered surfaces. This IS the cockpit's `CockpitMode::surfaces()`
//!     mapping, lifted out of compiled Rust into a serializable cell. The default
//!     ([`LayoutModel::cockpit_default`]) mirrors the real five-mode arrangement exactly.
//!   - the **view** — a titled column with a section per mode (the mode label + blurb) and a
//!     row per surface under it (its label + a `move` button whose click is the affordance
//!     the cockpit wires to relocating that surface). A pure function of the layout model.
//!
//! Because the layout is *data* (a [`LayoutModel`] = the card's `view_source` document), it
//! is **reshaped from within**: [`LayoutCard::reshape`] applies a structural layout gesture
//! ([`LayoutPatch`] — move a surface to another mode, add a surface, reorder within a mode,
//! relabel a mode) to the layout model, re-serializes it as a *receipted patch* with *blame*,
//! and leaves a real provenance receipt on the card's OWN cell's chain (the same
//! [`Applet`]-backed authorship turn the inspector/objects cards use). The arrangement
//! reshapes live; the edit is an accountable patch, not a recompile. **The cockpit then READS
//! this layout cell to render the rail + the modes' sub-navs** (the follow-on mount — see
//! [`LayoutCard::layout`] / [`LayoutModel::surfaces_of`]) instead of the hardcoded
//! `CockpitMode::surfaces()`.
//!
//! ## The cap tooth is kept
//!
//! A reshape is admitted only when `held` satisfies the card's `edit_authority`
//! ([`LayoutCard::authorized`], the proven [`dregg_cell::is_attenuation`] gate). An
//! unauthorized reshape — an attempt to move/add/reorder a surface the driver may not — is
//! refused in-band: no patch, no receipt, the arrangement unchanged. The structure of the
//! cockpit is as accountable as any other turn.

use dregg_cell::AuthRequired;
use dregg_doc::{Author, BlameLine};
use dregg_turn::TurnReceipt;
use serde::{Deserialize, Serialize};

use crate::applet::{pack_u64, Affordance, Applet, Slot};
use crate::card_editor::{
    ButtonProps, EditError, OnClick, TextProps, ViewEdit, ViewTree,
};
use crate::program_doc::ProgramSource;

/// The heap slot the layout card bumps to leave a provenance receipt for a *structural*
/// reshape (a layout-patch, which does not itself write a model field). Disjoint from the
/// inspector card's (14), the card-editor's (15), and the objects card's (16) authorship
/// slots, so a cockpit hosting all of them does not collide.
pub const LAYOUT_AUTHORSHIP_SLOT: Slot = 17;

/// One mode in the cockpit's layout — its label, its one-line blurb, and the ORDERED
/// surfaces re-homed under it. The serializable mirror of a `CockpitMode` row: the cockpit's
/// `CockpitMode::surfaces()` returns this row's `surfaces` (and `glyph`/`label`/`blurb`),
/// lifted out of compiled Rust into editable cell data.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LayoutMode {
    /// The mode's rail label (Inhabit / Author / Dev / Inspect / Operate). Stable — a
    /// surface MOVES between modes; the modes themselves are the five fixed rooms.
    pub mode: String,
    /// The mode's "what is this place" subtitle (the AOL-era wayfinding line).
    pub blurb: String,
    /// The surfaces re-homed under this mode, in sub-nav order. The first is the mode's
    /// primary (what a fresh rail click opens). Surface labels match the cockpit's
    /// `Tab::label()` so the cockpit can resolve a row back to its `Tab`.
    pub surfaces: Vec<String>,
}

/// **The cockpit's layout AS DATA** — the ordered five modes, each with its surfaces. This
/// is the editable cell that supersedes the hardcoded `CockpitMode::surfaces()`: the cockpit
/// reads it to render the rail (one entry per mode, in order) and each mode's sub-nav (its
/// surfaces, in order). A reshape ([`LayoutCard::reshape`]) edits THIS structure.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LayoutModel {
    /// The five modes in rail order (Inhabit first — the landing).
    pub modes: Vec<LayoutMode>,
}

impl LayoutModel {
    /// **The real cockpit layout** — the five-mode arrangement the cockpit ships with,
    /// mirrored EXACTLY from `starbridge-v2/src/cockpit/frame.rs` `CockpitMode::surfaces()`
    /// (the surface labels are the cockpit's `Tab::label()` strings). This is the default the
    /// layout card seeds; reshaping it from within is what moves a surface to another mode.
    pub fn cockpit_default() -> Self {
        LayoutModel {
            modes: vec![
                LayoutMode {
                    mode: "Inhabit".into(),
                    blurb: "your living world".into(),
                    surfaces: vec![
                        "HOME".into(),
                        "WONDER".into(),
                        "OBJECTS".into(),
                        "GRAPH".into(),
                    ],
                },
                LayoutMode {
                    mode: "Author".into(),
                    blurb: "make things".into(),
                    surfaces: vec![
                        "COMPOSER".into(),
                        "📄 DOCS".into(),
                        "EDITOR".into(),
                        "BUFFER".into(),
                        "WEB-OF-CELLS".into(),
                        "WHAT-LINKS-HERE".into(),
                        "⤳ SHARE".into(),
                    ],
                },
                LayoutMode {
                    mode: "Dev".into(),
                    blurb: "the IDE".into(),
                    surfaces: vec![
                        "TERMINAL".into(),
                        "SHELL".into(),
                        "⚙ DEVTOOLS".into(),
                        "🌐 WEB-SHELL".into(),
                        "SIMULATE".into(),
                        "LANES".into(),
                    ],
                },
                LayoutMode {
                    mode: "Inspect".into(),
                    blurb: "understand".into(),
                    surfaces: vec![
                        "INSPECTOR".into(),
                        "INSPECT-ACT".into(),
                        "WORKSPACE".into(),
                        "DEBUGGER".into(),
                        "REPLAY".into(),
                        "⏳ TIME".into(),
                        "PROOFS".into(),
                        "ORGANS".into(),
                    ],
                },
                LayoutMode {
                    mode: "Operate".into(),
                    blurb: "the machinery".into(),
                    surfaces: vec![
                        "AGENT".into(),
                        "SWARM".into(),
                        "POWERBOX".into(),
                        "CIPHERCLERK".into(),
                        "⚷ TRUST".into(),
                    ],
                },
            ],
        }
    }

    /// Parse a layout from a card's `view_source` JSON.
    pub fn from_json(json: &str) -> Result<Self, EditError> {
        serde_json::from_str(json).map_err(|e| EditError::BadView(format!("layout JSON: {e}")))
    }

    /// Serialize this layout to its canonical (pretty) JSON — the card's `view_source`. Pretty
    /// so the line-granular patches/blame have line structure to bite on.
    pub fn to_json(&self) -> String {
        serde_json::to_string_pretty(self).expect("layout serializes")
    }

    /// The mode labels in rail order — what the cockpit's left rail renders (one entry per
    /// mode, in this order).
    pub fn mode_order(&self) -> Vec<String> {
        self.modes.iter().map(|m| m.mode.clone()).collect()
    }

    /// **The surfaces re-homed under `mode`, in sub-nav order** — the cockpit reads THIS in
    /// place of the hardcoded `CockpitMode::surfaces()` to render a mode's sub-nav. Empty if
    /// no such mode (the cockpit degrades to its hardcoded fallback, never blank).
    pub fn surfaces_of(&self, mode: &str) -> Vec<String> {
        self.modes
            .iter()
            .find(|m| m.mode == mode)
            .map(|m| m.surfaces.clone())
            .unwrap_or_default()
    }

    /// The mode a surface currently lives under (the forward map — the inverse of
    /// [`Self::surfaces_of`]; the cockpit uses it so a `Go<Surface>` jump moves the rail to
    /// the right mode). `None` if the surface is in no mode.
    pub fn mode_of(&self, surface: &str) -> Option<String> {
        self.modes
            .iter()
            .find(|m| m.surfaces.iter().any(|s| s == surface))
            .map(|m| m.mode.clone())
    }

    /// Every surface across all modes, in (mode-order, sub-nav-order). The flattened roster —
    /// used to assert the reshape conserves the surface set (no surface lost or duplicated).
    pub fn all_surfaces(&self) -> Vec<String> {
        self.modes
            .iter()
            .flat_map(|m| m.surfaces.iter().cloned())
            .collect()
    }
}

/// A layout-reshape gesture — the structural change a [`LayoutCard::reshape`] applies to the
/// layout model before re-serializing it as a patch. Each is a real, accountable edit to the
/// cockpit's STRUCTURE.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LayoutPatch {
    /// **Move a surface to another mode** — relocate `surface` to the end of `to_mode`'s
    /// sub-nav (removing it from wherever it currently lives). The headline reshape: re-home a
    /// surface from one of the five rooms to another, live.
    MoveSurface { surface: String, to_mode: String },
    /// **Add a surface to a mode** — append a (new or relocated) `surface` to the end of
    /// `to_mode`'s sub-nav. If the surface already lives in another mode it is moved (no
    /// duplication); a fresh surface label simply lands here.
    AddSurface { surface: String, to_mode: String },
    /// **Reorder a surface within its mode** — move `surface` to sit immediately before
    /// `before` in the same mode's sub-nav. Reorders within one room (e.g. promote a surface
    /// to primary by moving it before the current first).
    ReorderSurface {
        mode: String,
        surface: String,
        before: String,
    },
    /// **Relabel a mode's blurb** — change a mode's one-line wayfinding subtitle (a cosmetic
    /// reshape of the chrome).
    RelabelMode { mode: String, blurb: String },
}

impl LayoutPatch {
    /// Apply this gesture to a layout model, returning whether it changed anything (so the
    /// caller can refuse a no-op reshape — e.g. moving a surface to the mode it is already in,
    /// or naming a mode that does not exist).
    fn apply(&self, model: &mut LayoutModel) -> bool {
        match self {
            LayoutPatch::MoveSurface { surface, to_mode }
            | LayoutPatch::AddSurface { surface, to_mode } => move_surface(model, surface, to_mode),
            LayoutPatch::ReorderSurface {
                mode,
                surface,
                before,
            } => reorder_surface(model, mode, surface, before),
            LayoutPatch::RelabelMode { mode, blurb } => relabel_mode(model, mode, blurb),
        }
    }
}

/// Move `surface` to the end of `to_mode`'s sub-nav, removing it from any mode it currently
/// lives in. Returns whether the layout changed (false if `to_mode` is unknown, or the
/// surface is already the last surface of `to_mode` and lives nowhere else).
fn move_surface(model: &mut LayoutModel, surface: &str, to_mode: &str) -> bool {
    if !model.modes.iter().any(|m| m.mode == to_mode) {
        return false; // a move to a non-existent mode is a no-op (the five rooms are fixed).
    }
    // A no-op iff the surface is ALREADY the sole tail of exactly `to_mode`.
    let already_there = model
        .modes
        .iter()
        .find(|m| m.mode == to_mode)
        .map(|m| m.surfaces.last().map(|s| s.as_str()) == Some(surface))
        .unwrap_or(false)
        && model.mode_of(surface).as_deref() == Some(to_mode);
    if already_there {
        return false;
    }
    // Remove the surface from wherever it is (at most one mode — modes partition surfaces).
    for m in model.modes.iter_mut() {
        m.surfaces.retain(|s| s != surface);
    }
    // Append it to the target mode.
    if let Some(m) = model.modes.iter_mut().find(|m| m.mode == to_mode) {
        m.surfaces.push(surface.to_string());
        return true;
    }
    false
}

/// Reorder `surface` to sit immediately before `before` within `mode`. Returns whether the
/// order changed (false if the mode/surface/anchor is missing, or it is already there).
fn reorder_surface(model: &mut LayoutModel, mode: &str, surface: &str, before: &str) -> bool {
    let Some(m) = model.modes.iter_mut().find(|m| m.mode == mode) else {
        return false;
    };
    let Some(from) = m.surfaces.iter().position(|s| s == surface) else {
        return false;
    };
    let Some(anchor) = m.surfaces.iter().position(|s| s == before) else {
        return false;
    };
    if from == anchor {
        return false; // a surface cannot reorder relative to itself.
    }
    let moved = m.surfaces.remove(from);
    // Recompute the anchor index after the removal (it shifts left if it was past `from`).
    let insert_at = m
        .surfaces
        .iter()
        .position(|s| s == before)
        .unwrap_or(m.surfaces.len());
    if insert_at == from {
        // No effective change (e.g. it already directly preceded `before`).
        m.surfaces.insert(from, moved);
        return false;
    }
    m.surfaces.insert(insert_at, moved);
    true
}

/// Relabel `mode`'s blurb. Returns whether it changed (false if the mode is missing or the
/// blurb is identical).
fn relabel_mode(model: &mut LayoutModel, mode: &str, blurb: &str) -> bool {
    if let Some(m) = model.modes.iter_mut().find(|m| m.mode == mode) {
        if m.blurb != blurb {
            m.blurb = blurb.to_string();
            return true;
        }
    }
    false
}

/// **The layout card** — a deos-js card whose state is the cockpit's mode→surface
/// arrangement (a [`LayoutModel`]), rendered as a view-tree (a section per mode, a row per
/// surface), and reshaped from within (each reshape a receipted cap-gated patch). The cockpit
/// reads its [`LayoutCard::layout`] to render the rail + sub-navs in place of the hardcoded
/// `CockpitMode::surfaces()`.
pub struct LayoutCard {
    /// The card's OWN sovereign cell — the substance a reshape receipts against (its
    /// authorship slot bumps via a real `SetField` turn). NOT a surface; the layout's chassis.
    card: Applet,
    /// The live layout model — the editable mode→surfaces arrangement (the cockpit's
    /// structure as data). The view-source is the JSON of this.
    model: LayoutModel,
    /// The layout card's view-source AS A DOCUMENT (a patch-history). The initial view is the
    /// serialized layout; every reshape appends a patch, so [`Self::blame`] attributes each
    /// layout line to its author.
    view: ProgramSource,
    /// The authority the card's driver holds — the cap a reshape is checked against.
    held: AuthRequired,
    /// The authority a reshape on THIS card requires (the authoring cap tooth). `held` must
    /// satisfy it ([`dregg_cell::is_attenuation`]).
    edit_authority: AuthRequired,
    /// The author every reshape patch is attributed to (the blame identity).
    author: Author,
}

impl LayoutCard {
    /// **Open the layout card** seeded with the real cockpit arrangement
    /// ([`LayoutModel::cockpit_default`]). `author` attributes the reshape patches; `held` is
    /// the driver's authority and `edit_authority` the cap a reshape requires. The card mints
    /// its OWN cell from `card_pk` (the provenance substance).
    pub fn open(
        card_pk: [u8; 32],
        author: Author,
        held: AuthRequired,
        edit_authority: AuthRequired,
    ) -> Self {
        Self::with_model(LayoutModel::cockpit_default(), card_pk, author, held, edit_authority)
    }

    /// **Open the layout card over an explicit layout model** — for a cockpit that has already
    /// reshaped its arrangement (the layout cell persists across sessions), or for a test.
    pub fn with_model(
        model: LayoutModel,
        card_pk: [u8; 32],
        author: Author,
        held: AuthRequired,
        edit_authority: AuthRequired,
    ) -> Self {
        let card = Applet::mint(card_pk, [0u8; 32], &[], Vec::new(), held.clone());
        let initial = model.to_json();
        let view = ProgramSource::seed(author, &initial);
        LayoutCard {
            card,
            model,
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

    /// **The live layout** — the cockpit reads THIS to render the rail (mode order) + each
    /// mode's sub-nav ([`LayoutModel::surfaces_of`]) in place of the hardcoded
    /// `CockpitMode::surfaces()`. A reshape advances it.
    pub fn layout(&self) -> &LayoutModel {
        &self.model
    }

    /// The layout card's current view source (the document fold) — the JSON of the layout the
    /// cockpit reads and a renderer paints.
    pub fn view_source(&self) -> String {
        self.view.view_source()
    }

    /// The layout card's view-tree (the re-folded shape a renderer paints) — a section per
    /// mode + a row per surface, generated from the current layout model.
    pub fn view_tree(&self) -> Result<ViewTree, EditError> {
        Ok(layout_view_for(&self.model))
    }

    /// The blame over the layout card's view source — who reshaped each layout line, in which
    /// patch (the "accountable patch, not a recompile" face for the cockpit's structure).
    pub fn blame(&self) -> Vec<BlameLine> {
        self.view.blame()
    }

    /// Whether the card is authorized to reshape the layout (the authoring cap tooth).
    fn authorized(&self) -> bool {
        dregg_cell::is_attenuation(&self.held, &self.edit_authority)
    }

    /// Fire a real `SetField` provenance turn bumping the card's authorship slot — how a
    /// *structural* reshape (a layout-patch, which does not itself write a model field) still
    /// lands a receipt on the card's chain. Gated on the SAME `edit_authority` the cap tooth
    /// already cleared.
    fn provenance_turn(&mut self) -> Result<TurnReceipt, EditError> {
        let next = self.card.model().field_u64(LAYOUT_AUTHORSHIP_SLOT) + 1;
        self.card.register_affordance(Affordance {
            name: "__layout_authorship__".into(),
            required: self.edit_authority.clone(),
            apply: Box::new(move |_model, _arg| vec![(LAYOUT_AUTHORSHIP_SLOT, pack_u64(next))]),
        });
        self.card
            .fire("__layout_authorship__", 0)
            .map_err(|e| EditError::Fire(e.to_string()))
    }

    /// **RESHAPE THE LAYOUT FROM WITHIN — the keystone.** Apply a structural layout gesture
    /// ([`LayoutPatch`] — move a surface to another mode, add a surface, reorder within a
    /// mode, relabel a mode) to the cockpit's own arrangement, append the result as a PATCH to
    /// the card's `view_source` document, and leave a provenance receipt on the card's chain.
    ///
    /// The result is the re-folded view-tree (a renderer re-paints it — the rail/sub-navs
    /// reshape live; the cockpit re-reads [`Self::layout`]), the blame (each layout line
    /// attributed — an *accountable patch, not a recompile*), and the provenance receipt.
    /// Refused in-band if `held` does not satisfy the card's `edit_authority`, or if the
    /// reshape changed nothing.
    pub fn reshape(&mut self, patch: LayoutPatch) -> Result<ViewEdit, EditError> {
        if !self.authorized() {
            return Err(EditError::Unauthorized);
        }

        let mut model = self.model.clone();
        if !patch.apply(&mut model) {
            return Err(EditError::NoOp);
        }
        self.model = model;
        let new_source = self.model.to_json();

        // PATCH — append to the layout document (NOT a wholesale rewrite), so blame attributes
        // the reshaped lines to this card's author.
        self.view.edit(self.author, &new_source);

        // A structural reshape still lands a verified receipt on the card's chain.
        let receipt = self.provenance_turn()?;

        Ok(ViewEdit {
            tree: layout_view_for(&self.model),
            blame: self.view.blame(),
            receipt,
        })
    }
}

// ── view-tree generation (the layout card's view IS the arrangement's data) ─────────────────

/// **Generate the layout view-tree** from a [`LayoutModel`]: a titled column with a section
/// per mode (the mode label + its blurb as text) and one row per surface under it (the
/// surface label + a `move` button whose click is the affordance the cockpit wires to
/// relocating that surface). The substance-agnostic core both [`LayoutCard::view_tree`] and
/// the public [`layout_view`] use.
fn layout_view_for(model: &LayoutModel) -> ViewTree {
    let mut top: Vec<ViewTree> = Vec::new();
    top.push(text(&format!(
        "Cockpit layout · {} modes · {} surfaces",
        model.modes.len(),
        model.all_surfaces().len()
    )));

    for m in &model.modes {
        let mut section: Vec<ViewTree> = vec![
            // The mode header (its name) + its blurb. The name is a relabel/move anchor; the
            // blurb is what `RelabelMode` rewrites.
            text(&format!("{} · {}", m.mode, m.blurb)),
        ];
        if m.surfaces.is_empty() {
            section.push(text("(no surfaces)"));
        } else {
            for surface in &m.surfaces {
                // Each surface is a row: its label + a `move` affordance whose click the
                // cockpit wires to relocating this surface (the `arg`-bearing turn the rung-3
                // mount dispatches to `LayoutCard::reshape(MoveSurface { .. })`).
                section.push(ViewTree::Row {
                    children: vec![
                        text(surface),
                        button("move", &format!("move:{surface}"), 1),
                    ],
                });
            }
        }
        top.push(ViewTree::VStack { children: section });
    }

    ViewTree::VStack { children: top }
}

/// **Generate the layout view-tree (the public entry).** A renderer (`deos-view`) parses the
/// JSON of this and paints it over the layout card; the per-surface `move` buttons map to
/// relocating that surface, the sections to the live mode→surface arrangement.
pub fn layout_view(model: &LayoutModel) -> ViewTree {
    layout_view_for(model)
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

#[cfg(test)]
mod tests {
    use super::*;

    fn layout_card() -> LayoutCard {
        LayoutCard::open(
            [0xCB; 32],
            Author(42),
            /*held=*/ AuthRequired::None,
            /*edit_authority=*/ AuthRequired::Signature,
        )
    }

    // (a) THE DEFAULT — the layout card mirrors the real cockpit arrangement EXACTLY (the
    //     five modes, in order, with their surfaces). This IS the data the cockpit reads in
    //     place of the hardcoded `CockpitMode::surfaces()`.
    #[test]
    fn the_default_layout_mirrors_the_cockpit_five_mode_arrangement() {
        let card = layout_card();
        let layout = card.layout();

        // The five modes in rail order.
        assert_eq!(
            layout.mode_order(),
            vec!["Inhabit", "Author", "Dev", "Inspect", "Operate"],
            "the five modes in rail order (Inhabit first — the landing)"
        );

        // Each mode's surfaces match `CockpitMode::surfaces()` (counts + membership).
        assert_eq!(layout.surfaces_of("Inhabit").len(), 4);
        assert_eq!(layout.surfaces_of("Author").len(), 7);
        assert_eq!(layout.surfaces_of("Dev").len(), 6);
        assert_eq!(layout.surfaces_of("Inspect").len(), 8);
        assert_eq!(layout.surfaces_of("Operate").len(), 5);

        // The surfaces partition: 30 total (= the cockpit's `Tab::ALL.len()`), no duplicates.
        let all = layout.all_surfaces();
        assert_eq!(all.len(), 30, "the five modes' surfaces sum to the full set");
        let mut uniq = all.clone();
        uniq.sort();
        uniq.dedup();
        assert_eq!(uniq.len(), all.len(), "no surface appears in two modes");

        // The forward map (a surface → its mode) resolves — the cockpit uses it to move the
        // rail on a `Go<Surface>` jump.
        assert_eq!(layout.mode_of("OBJECTS").as_deref(), Some("Inhabit"));
        assert_eq!(layout.mode_of("EDITOR").as_deref(), Some("Author"));
        assert_eq!(layout.mode_of("AGENT").as_deref(), Some("Operate"));
    }

    // (b) THE VIEW — the layout renders as a section per mode + a row per surface (a `move`
    //     affordance each). This is the data-defined chrome a renderer paints.
    #[test]
    fn the_layout_renders_the_current_mode_to_surface_arrangement() {
        let card = layout_card();
        let tree = card.view_tree().expect("the layout view parses");

        // A header counting the arrangement.
        assert!(
            tree.walk()
                .iter()
                .any(|n| n.label() == Some("Cockpit layout · 5 modes · 30 surfaces")),
            "the header counts the live arrangement"
        );
        // Each mode is a labeled section.
        for (mode, blurb) in [
            ("Inhabit", "your living world"),
            ("Operate", "the machinery"),
        ] {
            assert!(
                tree.walk()
                    .iter()
                    .any(|n| n.label() == Some(&format!("{mode} · {blurb}"))),
                "the {mode} section is labeled with its blurb"
            );
        }
        // Each surface has a `move` affordance (the cockpit wires its click to relocation).
        assert!(
            tree.has_button_for("move:OBJECTS"),
            "the OBJECTS surface carries a `move` affordance"
        );
        assert!(
            tree.has_button_for("move:AGENT"),
            "the AGENT surface carries a `move` affordance"
        );
    }

    // (c) MOVE-SURFACE — the keystone reshape: relocate a surface to another mode, live. A
    //     receipted patch with blame; the arrangement (the data the cockpit reads) changes.
    #[test]
    fn a_move_surface_reshape_relocates_a_surface_receipted_with_blame() {
        let mut card = layout_card();
        let source_before = card.view_source();
        let blame_before = card.blame().len();
        assert_eq!(card.layout().mode_of("OBJECTS").as_deref(), Some("Inhabit"));

        // MOVE the OBJECTS surface from Inhabit to Author, from within.
        let edit = card
            .reshape(LayoutPatch::MoveSurface {
                surface: "OBJECTS".into(),
                to_mode: "Author".into(),
            })
            .expect("the authorized move-surface reshape is admitted");

        // The arrangement (the data the cockpit reads) changed: OBJECTS now lives in Author,
        // gone from Inhabit.
        assert_eq!(
            card.layout().mode_of("OBJECTS").as_deref(),
            Some("Author"),
            "OBJECTS was re-homed under Author"
        );
        assert!(
            !card.layout().surfaces_of("Inhabit").contains(&"OBJECTS".to_string()),
            "OBJECTS no longer lives in Inhabit"
        );
        assert!(
            card.layout().surfaces_of("Author").contains(&"OBJECTS".to_string()),
            "OBJECTS now lives in Author (the cockpit reads this for the sub-nav)"
        );

        // The surface set is CONSERVED — a move loses no surface and duplicates none.
        let all = card.layout().all_surfaces();
        assert_eq!(all.len(), 30, "the move conserved the surface count");
        let mut uniq = all.clone();
        uniq.sort();
        uniq.dedup();
        assert_eq!(uniq.len(), 30, "no surface duplicated by the move");

        // The view (the rendered chrome) reshaped too.
        assert_ne!(
            card.view_source(),
            source_before,
            "the layout view-source changed (the chrome reshaped from within)"
        );
        assert!(
            edit.tree.has_button_for("move:OBJECTS"),
            "the re-folded view still carries the moved surface (now under Author)"
        );

        // The reshape is a RECEIPTED PATCH — a provenance turn landed on the card's chain.
        assert_ne!(
            edit.receipt.receipt_hash(),
            [0u8; 32],
            "the structural reshape left a real provenance receipt"
        );
        // BLAME attributes the reshape to its author.
        assert!(
            card.blame().iter().any(|l| l.author == Author(42)),
            "the layout reshape is blamed on its author (the accountable patch)"
        );
        assert!(
            card.blame().len() >= blame_before,
            "the reshape recorded a patch on the layout document"
        );
        assert_eq!(
            card.card().receipt_count(),
            1,
            "exactly one provenance receipt for the reshape"
        );
    }

    // (d) ADD + REORDER — a surface can be added to a mode and reordered within it (promote to
    //     primary), each a receipted reshape.
    #[test]
    fn add_and_reorder_reshape_the_arrangement() {
        let mut card = layout_card();

        // ADD a fresh surface (a new card the agent authored) to Operate.
        card.reshape(LayoutPatch::AddSurface {
            surface: "WATCHTOWER".into(),
            to_mode: "Operate".into(),
        })
        .expect("add a fresh surface to Operate");
        assert_eq!(
            card.layout().mode_of("WATCHTOWER").as_deref(),
            Some("Operate"),
            "the fresh surface landed in Operate"
        );
        assert_eq!(
            card.layout().surfaces_of("Operate").len(),
            6,
            "Operate grew from 5 to 6 surfaces"
        );

        // REORDER it to the front of Operate (promote it to the mode's primary).
        card.reshape(LayoutPatch::ReorderSurface {
            mode: "Operate".into(),
            surface: "WATCHTOWER".into(),
            before: "AGENT".into(),
        })
        .expect("promote the surface to primary");
        assert_eq!(
            card.layout().surfaces_of("Operate").first().map(|s| s.as_str()),
            Some("WATCHTOWER"),
            "the surface is now Operate's primary (the cockpit opens it on a rail click)"
        );

        assert_eq!(
            card.card().receipt_count(),
            2,
            "two reshapes → two provenance receipts"
        );
    }

    // (e) A NO-OP RESHAPE IS REFUSED — moving a surface to the mode it already tails, or
    //     naming a mode that does not exist, changes nothing and leaves no receipt.
    #[test]
    fn a_no_op_reshape_is_refused() {
        let mut card = layout_card();
        // GRAPH already tails Inhabit (Home, Wonder, Objects, GRAPH) — moving it there is a
        // no-op.
        let err = card.reshape(LayoutPatch::MoveSurface {
            surface: "GRAPH".into(),
            to_mode: "Inhabit".into(),
        });
        assert!(matches!(err, Err(EditError::NoOp)), "a no-op move is refused");

        // A move to a non-existent mode is a no-op (the five rooms are fixed).
        let err2 = card.reshape(LayoutPatch::MoveSurface {
            surface: "GRAPH".into(),
            to_mode: "Nowhere".into(),
        });
        assert!(matches!(err2, Err(EditError::NoOp)), "a move to a phantom mode is refused");

        assert_eq!(
            card.card().receipt_count(),
            0,
            "no receipt on a no-op reshape"
        );
    }

    // (f) THE CAP TOOTH — an unauthorized reshape is refused in-band (no patch, no receipt).
    #[test]
    fn an_unauthorized_reshape_is_refused_in_band() {
        // held=Signature does NOT satisfy edit_authority=Proof → the authoring tooth refuses.
        let mut card = LayoutCard::open(
            [0xBA; 32],
            Author(7),
            /*held=*/ AuthRequired::Signature,
            /*edit_authority=*/ AuthRequired::Proof,
        );
        let before = card.view_source();
        let err = card.reshape(LayoutPatch::MoveSurface {
            surface: "OBJECTS".into(),
            to_mode: "Author".into(),
        });
        assert!(
            matches!(err, Err(EditError::Unauthorized)),
            "an over-reach reshape is refused by the cap tooth"
        );
        assert_eq!(
            card.view_source(),
            before,
            "nothing changed (no patch on an unauthorized reshape)"
        );
        assert_eq!(
            card.layout().mode_of("OBJECTS").as_deref(),
            Some("Inhabit"),
            "the arrangement is unchanged (OBJECTS still in Inhabit)"
        );
        assert_eq!(
            card.card().receipt_count(),
            0,
            "no receipt on an unauthorized reshape"
        );
    }

    // (g) ROUND-TRIP — the layout serializes to its view-source JSON and back, identically
    //     (the cockpit can persist + reload the arrangement cell across sessions).
    #[test]
    fn the_layout_round_trips_through_its_view_source() {
        let card = layout_card();
        let json = card.view_source();
        let reloaded = LayoutModel::from_json(&json).expect("the view-source parses as a layout");
        assert_eq!(
            &reloaded,
            card.layout(),
            "the layout round-trips through its serialized view-source"
        );
    }
}
