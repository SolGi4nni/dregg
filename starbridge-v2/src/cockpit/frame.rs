//! THE COHERENT FRAME — the persistent chrome + the FIVE MODES.
//!
//! `docs/deos/COCKPIT-UX.md`. The ~20 peer surfaces (the flat `Go<Surface>`
//! palette) are re-framed into ONE stable chrome with FIVE modes:
//!
//!   * a TOP BAR — the identity cell + its cap-badge · the live ledger clock
//!     (height + the latest receipt) · the ⌘K palette summon. Always present.
//!   * a LEFT RAIL of the FIVE MODES — one click switches the whole content
//!     pane's intent (not 20 doors; five rooms).
//!   * a MAIN PANE — the active surface for the current mode, with a small
//!     sub-nav of the mode's surfaces.
//!   * a collapsible DEV DOCK at the bottom (⌘J toggles it) — the dev workspace
//!     strip, available in any mode.
//!
//! The frame is purely a RE-FRAMING: no surface is deleted. Each [`Tab`] is
//! re-homed under exactly one [`CockpitMode`]; the existing per-tab renders
//! ([`Cockpit::panel_for_tab`]) are unchanged. The palette's `Go<Surface>`
//! commands still work — `set_tab` now also moves the rail to the surface's mode.

use super::*;

/// The deterministic provenance pk for the cockpit's layout cell (the substance a
/// `move:` reshape receipts against). A fixed identity so the layout cell's chain is
/// stable across re-mounts of the cockpit.
#[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
const LAYOUT_CARD_PK: [u8; 32] = [0x1A; 32];

/// The author every layout reshape patch is attributed to (the blame identity on the
/// layout document) — the operator reshaping their own chrome.
#[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
const LAYOUT_CARD_AUTHOR: u64 = 0x1A;

/// The FIVE MODES — the coherence the rail teaches once. Each groups the
/// surfaces by INTENT (`docs/deos/COCKPIT-UX.md` §"The five modes").
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CockpitMode {
    /// INHABIT — *your living world.* The home garden, the cells as clickable
    /// objects, the ocap graph. The landing.
    Inhabit,
    /// AUTHOR — *make things.* The composer, the document/card surfaces, the
    /// buffer — the hyperdreggmedia authoring layer.
    Author,
    /// DEV — *the IDE.* Editor (deos-zed), terminal, shell, devtools, web-shell,
    /// simulate — one coherent workspace. The dev dock is this mode's strip.
    Dev,
    /// INSPECT — *understand.* The moldable inspector + its lanes, debugger,
    /// replay, proofs, organs — point at any object, see it every way, rewind it.
    Inspect,
    /// OPERATE — *the machinery.* Agent, swarm, powerbox, cipherclerk — the
    /// cap/agent/delegation controls.
    Operate,
}

impl CockpitMode {
    /// The modes in rail order (Inhabit first — the landing).
    pub const ALL: [CockpitMode; 5] = [
        CockpitMode::Inhabit,
        CockpitMode::Author,
        CockpitMode::Dev,
        CockpitMode::Inspect,
        CockpitMode::Operate,
    ];

    /// The rail glyph + label.
    pub fn glyph(self) -> &'static str {
        match self {
            CockpitMode::Inhabit => "🏡",
            CockpitMode::Author => "✎",
            CockpitMode::Dev => "⌨",
            CockpitMode::Inspect => "🔍",
            CockpitMode::Operate => "⚙",
        }
    }

    pub fn label(self) -> &'static str {
        match self {
            CockpitMode::Inhabit => "Inhabit",
            CockpitMode::Author => "Author",
            CockpitMode::Dev => "Dev",
            CockpitMode::Inspect => "Inspect",
            CockpitMode::Operate => "Operate",
        }
    }

    /// Resolve a mode label (a [`Self::label`] string) back to its [`CockpitMode`]
    /// — the inverse of [`Self::label`]. How the cockpit maps a layout cell's mode
    /// rows (the [`deos_js::LayoutModel::mode_order`] strings) back to the rail's
    /// modes. `None` for an unknown label (the layout names a mode the cockpit does
    /// not have — the read-side degrades to the hardcoded `ALL`).
    pub fn from_label(label: &str) -> Option<CockpitMode> {
        CockpitMode::ALL.into_iter().find(|m| m.label() == label)
    }

    /// A one-line "what is this place" subtitle (the AOL-era wayfinding).
    pub fn blurb(self) -> &'static str {
        match self {
            CockpitMode::Inhabit => "your living world",
            CockpitMode::Author => "make things",
            CockpitMode::Dev => "the IDE",
            CockpitMode::Inspect => "understand",
            CockpitMode::Operate => "the machinery",
        }
    }

    /// The surfaces re-homed under this mode, in sub-nav order. NO surface is
    /// deleted — every [`Tab`] belongs to exactly one mode (see [`Tab::mode`]),
    /// and this is the inverse grouping the sub-nav renders.
    pub fn surfaces(self) -> &'static [Tab] {
        match self {
            // INHABIT — the living world / landing.
            CockpitMode::Inhabit => &[Tab::Home, Tab::Wonder, Tab::Objects, Tab::Graph],
            // AUTHOR — the hyperdreggmedia authoring layer.
            CockpitMode::Author => &[
                Tab::Composer,
                Tab::Docs,
                Tab::Editor,
                Tab::Buffer,
                Tab::WebOfCells,
                Tab::LinksHere,
                Tab::Share,
            ],
            // DEV — the IDE workspace (this mode's surfaces ARE the dock content).
            CockpitMode::Dev => &[
                Tab::Terminal,
                Tab::Shell,
                Tab::Devtools,
                Tab::WebShell,
                Tab::Simulate,
                Tab::Lanes,
            ],
            // INSPECT — understand / rewind.
            CockpitMode::Inspect => &[
                Tab::Moldable,
                Tab::InspectAct,
                Tab::Workspace,
                Tab::Debugger,
                Tab::Replay,
                Tab::Time,
                Tab::Proofs,
                Tab::Organs,
            ],
            // OPERATE — the cap/agent/delegation machinery.
            CockpitMode::Operate => &[
                Tab::Agent,
                Tab::Swarm,
                Tab::Powerbox,
                Tab::Cipherclerk,
                Tab::ServiceExplorer,
                Tab::Trust,
            ],
        }
    }

    /// The mode's PRIMARY surface — what a fresh click on the rail opens.
    pub fn primary(self) -> Tab {
        self.surfaces()[0]
    }
}

impl Tab {
    /// Which [`CockpitMode`] this surface is re-homed under. The forward map
    /// (the inverse of [`CockpitMode::surfaces`]); used so a `set_tab` (a palette
    /// `Go<Surface>` or a nav-history restore) moves the rail to the right mode.
    pub fn mode(self) -> CockpitMode {
        for m in CockpitMode::ALL {
            if m.surfaces().contains(&self) {
                return m;
            }
        }
        // Every Tab is grouped above; a new Tab without a home lands in Inhabit
        // (never blank). The `every_tab_has_a_mode` test guards against the gap.
        CockpitMode::Inhabit
    }
}

impl Cockpit {
    // === THE LAYOUT CELL — the cockpit's structure as editable DATA (rung 3) ===
    //
    // The rail + sub-navs + the `Go<Surface>` rail-highlight READ these three
    // resolvers instead of the hardcoded `CockpitMode::surfaces`/`ALL`/`Tab::mode`.
    // Each resolver reads the live [`deos_js::LayoutCard`] cell (built lazily by
    // [`Self::ensure_layout_card`], the cockpit's structure as a serializable
    // `LayoutModel`), resolving the cell's string labels — which ARE the cockpit's
    // own [`CockpitMode::label`]/[`Tab::label`] strings — back to the renderable
    // enums. The fallback to the hardcoded map is total: if the layout cell is
    // absent (the gpui-free / `card-pane`-off build) or names a mode/surface the
    // cockpit has no enum for, the read degrades to the compiled arrangement, so the
    // rail is NEVER blank.

    /// **ENSURE THE LAYOUT CELL (rung 3) is built.** Called on the paint path (the same
    /// place the inspector/mode cards mount), seeded with [`deos_js::LayoutModel::cockpit_default`]
    /// — the serialized mirror of the hardcoded [`CockpitMode::surfaces`] arrangement, so the
    /// first frame's rail is identical to the compiled one. Idempotent: built once, then the
    /// rail/sub-navs read it and a `move:` affordance reshapes it in place.
    #[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
    pub(crate) fn ensure_layout_card(&mut self) {
        if self.layout_card.is_some() {
            return;
        }
        // The operator's authority a reshape fires under — `Signature` (the attenuated
        // operator hand the inspector/mode cards mount under). It satisfies the card's
        // `edit_authority` (also `Signature`), so an operator reshape-from-within is
        // authorized; an unauthorized hand would be refused in-band by the same
        // `is_attenuation` cap tooth.
        let held = dregg_cell::AuthRequired::Signature;
        self.layout_card = Some(deos_js::LayoutCard::open(
            LAYOUT_CARD_PK,
            deos_js::Author(LAYOUT_CARD_AUTHOR),
            held.clone(),
            /*edit_authority=*/ held,
        ));
    }

    /// The modes in rail order — READ from the layout cell ([`deos_js::LayoutModel::mode_order`],
    /// resolving each label → [`CockpitMode`]), falling back to the hardcoded [`CockpitMode::ALL`]
    /// when the layout cell is absent or yields no resolvable modes. What [`Self::mode_rail`]
    /// renders.
    pub(crate) fn layout_mode_order(&self) -> Vec<CockpitMode> {
        #[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
        if let Some(card) = self.layout_card.as_ref() {
            let order: Vec<CockpitMode> = card
                .layout()
                .mode_order()
                .iter()
                .filter_map(|label| CockpitMode::from_label(label))
                .collect();
            if !order.is_empty() {
                return order;
            }
        }
        CockpitMode::ALL.to_vec()
    }

    /// The surfaces re-homed under `mode`, in sub-nav order — READ from the layout cell
    /// ([`deos_js::LayoutModel::surfaces_of`], resolving each surface label → [`Tab`] via
    /// [`Tab::from_label`]), falling back to the hardcoded [`CockpitMode::surfaces`] when the
    /// layout cell is absent or yields no resolvable surfaces for the mode. What
    /// [`Self::mode_subnav`] renders.
    pub(crate) fn layout_surfaces_of(&self, mode: CockpitMode) -> Vec<Tab> {
        #[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
        if let Some(card) = self.layout_card.as_ref() {
            let surfaces: Vec<Tab> = card
                .layout()
                .surfaces_of(mode.label())
                .iter()
                .filter_map(|label| Tab::from_label(label))
                .collect();
            if !surfaces.is_empty() {
                return surfaces;
            }
        }
        mode.surfaces().to_vec()
    }

    /// The mode a surface currently lives under — READ from the layout cell
    /// ([`deos_js::LayoutModel::mode_of`], resolving the mode label → [`CockpitMode`]), falling
    /// back to the hardcoded [`Tab::mode`] when the layout cell is absent or does not place the
    /// surface. How [`Self::active_mode`] keeps the rail highlight on a `Go<Surface>` jump.
    pub(crate) fn layout_mode_of(&self, surface: Tab) -> CockpitMode {
        #[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
        if let Some(card) = self.layout_card.as_ref() {
            if let Some(mode) = card
                .layout()
                .mode_of(surface.label())
                .and_then(|label| CockpitMode::from_label(&label))
            {
                return mode;
            }
        }
        surface.mode()
    }

    /// The mode's PRIMARY surface (its first in layout order) — what a fresh rail click opens.
    /// READ from the layout cell (the first of [`Self::layout_surfaces_of`]), falling back to
    /// [`CockpitMode::primary`].
    pub(crate) fn layout_primary(&self, mode: CockpitMode) -> Tab {
        self.layout_surfaces_of(mode)
            .first()
            .copied()
            .unwrap_or_else(|| mode.primary())
    }

    /// **RESHAPE THE COCKPIT'S STRUCTURE FROM WITHIN — the rung-3 affordance.** Move
    /// `surface` to another mode by dispatching [`deos_js::LayoutCard::reshape`] with a
    /// [`deos_js::LayoutPatch::MoveSurface`] on the live layout cell (a receipted, cap-gated
    /// patch with blame), then repaint so the rail/sub-navs re-render from the reshaped cell.
    /// The `move:<SURFACE>` button the layout card renders wires here. Fail-soft: a refusal
    /// (unauthorized / no-op / no layout cell) is reported to the outcome banner, the
    /// arrangement unchanged.
    #[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
    pub(crate) fn reshape_layout_move(
        &mut self,
        surface: Tab,
        to_mode: CockpitMode,
        cx: &mut Context<Self>,
    ) {
        self.ensure_layout_card();
        let Some(card) = self.layout_card.as_mut() else {
            return;
        };
        match card.reshape(deos_js::LayoutPatch::MoveSurface {
            surface: surface.label().to_string(),
            to_mode: to_mode.label().to_string(),
        }) {
            Ok(_edit) => {
                self.last_outcome = Some(format!(
                    "layout reshaped · {} → {} (receipted)",
                    surface.label(),
                    to_mode.label()
                ));
            }
            Err(e) => {
                self.last_outcome = Some(format!("layout reshape refused: {e:?}"));
            }
        }
        cx.notify();
    }

    /// Switch the active MODE (a rail click) — opens the mode's primary surface
    /// (which moves the witnessed tab via [`Self::set_tab`]). The rail highlight
    /// then derives from the surface's mode ([`Self::active_mode`], read off the
    /// layout cell), so there is no separate mode state to drift. The primary is
    /// read off the layout cell ([`Self::layout_primary`]), so a reshape that
    /// reorders a mode's surfaces changes which surface a rail click opens.
    pub(crate) fn set_mode(&mut self, mode: CockpitMode, cx: &mut Context<Self>) {
        self.set_tab(self.layout_primary(mode), cx);
    }

    /// Toggle the collapsible DEV DOCK (⌘J) — the persistent dev strip available
    /// in any mode.
    pub(crate) fn toggle_dock(&mut self, cx: &mut Context<Self>) {
        self.dock_open = !self.dock_open;
        cx.notify();
    }

    /// Mark this cockpit as a FIRST RUN — show the calm sparse first-view (a warm
    /// welcome + a few cells + ONE "try this") instead of the full 5-mode wall.
    /// Login calls this for a brand-new image; the headless bake calls it to
    /// capture the first-view. Idempotent; takes effect on the next paint.
    pub fn set_first_run(&mut self, first_run: bool) {
        self.first_run = first_run;
    }

    /// DISMISS the first-run overlay — the operator chose "explore" (or fired the
    /// "try this" affordance and is ready for the full frame). Reveals the full
    /// 5-mode chrome. One-way: the wall is now familiar.
    pub(crate) fn dismiss_first_run(&mut self, cx: &mut Context<Self>) {
        self.first_run = false;
        cx.notify();
    }

    /// THE CALM FIRST-VIEW — what a first-timer meets in their brand-new world:
    /// not the 30-surface wall, but a breathing landing. A warm welcome, a FEW of
    /// their own cells as friendly clickable rows, ONE gentle "try this" (fire it
    /// → a real verified turn happens → delight), and a quiet "explore everything"
    /// that reveals the full frame. Progressive disclosure — the five modes + dev
    /// tooling are discoverable, not dumped. Rendered as the whole window body when
    /// [`Self::first_run`]; the full frame returns the instant they explore.
    pub(crate) fn first_view(&self, cx: &mut Context<Self>) -> impl IntoElement {
        // A FEW of the owner's cells (the curated handful, not the full ledger) —
        // their three anchors, named for a first-timer (their home, the treasury,
        // a service they hold). Friendly, clickable, balance-bearing.
        let [treasury, service, user] = self.anchors;
        let w = self.world.borrow();
        // A bullet from the covered ASCII set — renders in the windowed build AND
        // the headless fallback font, so the welcome reads calm everywhere (no
        // tofu). The friendly NAME carries the meaning; the dot just anchors the row.
        let curated: Vec<(CellId, &'static str, &'static str)> = vec![
            (user, "•", "your home"),
            (treasury, "•", "the treasury"),
            (service, "•", "a service you hold"),
        ];
        let mut cell_cards = div().flex().flex_col().gap_2();
        for (id, glyph, name) in curated {
            let bal = w.ledger().get(&id).map(|c| c.state.balance()).unwrap_or(0);
            cell_cards = cell_cards.child(
                div()
                    .id(SharedString::from(format!(
                        "first-cell-{}",
                        reflect::short_hex(id.as_bytes())
                    )))
                    .flex()
                    .items_center()
                    .justify_between()
                    .w(px(360.))
                    .px_3()
                    .py_2()
                    .rounded_md()
                    .bg(theme::panel())
                    .border_1()
                    .border_color(theme::border())
                    .cursor_pointer()
                    .hover(|s| s.bg(theme::panel_hi()))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev, _w, cx| {
                            // Clicking a cell selects it AND reveals the full frame
                            // (the inspector shows what they clicked) — a gentle slide
                            // into the world rather than a wall up front.
                            this.selection = Selection::Cell(id);
                            this.first_run = false;
                            cx.notify();
                        }),
                    )
                    .child(
                        div()
                            .flex()
                            .items_center()
                            .gap_2()
                            .child(div().text_lg().child(SharedString::from(glyph)))
                            .child(
                                div()
                                    .text_color(theme::text())
                                    .child(SharedString::from(name)),
                            ),
                    )
                    .child(pill(format!("{bal}"), theme::muted())),
            );
        }
        drop(w);

        div()
            .id("first-view")
            .size_full()
            .flex()
            .flex_col()
            .items_center()
            .justify_center()
            .gap_6()
            .bg(theme::bg())
            .text_color(theme::text())
            // The warm welcome — "this is your world".
            .child(
                div()
                    .flex()
                    .flex_col()
                    .items_center()
                    .gap_2()
                    .child(
                        div()
                            .text_2xl()
                            .text_color(theme::accent())
                            .child("welcome to your world"),
                    )
                    .child(
                        div()
                            .max_w(px(440.))
                            .text_sm()
                            .text_color(theme::muted())
                            .child(
                                "everything here is yours — living objects you can click, \
                                 hold, and change. nothing is set in stone; every change \
                                 is a verified move you can always trace.",
                            ),
                    ),
            )
            // A FEW of their cells (the curated handful) — click to meet one.
            .child(
                div()
                    .flex()
                    .flex_col()
                    .items_center()
                    .gap_2()
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::muted())
                            .child("a few things you hold —"),
                    )
                    .child(cell_cards),
            )
            // ONE gentle "try this" — fires a REAL verified turn (treasury → home)
            // on the live World, then reveals the full frame so they SEE it land.
            .child(
                div()
                    .id("first-try-this")
                    .px(px(24.))
                    .py(px(10.))
                    .rounded_md()
                    .bg(theme::accent())
                    .text_color(theme::bg())
                    .cursor_pointer()
                    .hover(|s| s.opacity(0.9))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(|this, _ev, _w, cx| {
                            // A real cap-gated turn through the embedded executor —
                            // the delight is that it genuinely HAPPENS (a receipt,
                            // a balance moved) — then the full frame reveals so they
                            // watch it land in the live image.
                            this.run_demo_transfer(cx);
                            this.first_run = false;
                            cx.notify();
                        }),
                    )
                    .child("try this — move a little value into your home  →"),
            )
            // MAKE A THING — the step past "fire a turn": one click mints a real
            // editable card that is YOURS, and drops into the first-card view to
            // press + edit it live. Present only on the card-pane build (the
            // authoring machinery); the helper returns nothing otherwise.
            .children(self.first_card_invite(cx))
            // The quiet door to everything else — present, not shoved.
            .child(
                div()
                    .id("first-explore")
                    .text_xs()
                    .text_color(theme::muted())
                    .cursor_pointer()
                    .hover(|s| s.text_color(theme::accent()))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(|this, _ev, _w, cx| this.dismiss_first_run(cx)),
                    )
                    .child("explore everything →"),
            )
    }

    /// THE "MAKE A THING" INVITE on the calm first-view — one warm affordance that
    /// mints a real editable card (the stranger's own) and drops into the first-card
    /// view. Returned as an `Option` child so `first_view` includes it ONLY on the
    /// card-pane build (the authoring machinery). On the non-card build the
    /// [`Self::first_card_invite`] stub returns `None`, so the first-view is unchanged.
    #[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
    pub(crate) fn first_card_invite(&self, cx: &mut Context<Self>) -> Option<gpui::AnyElement> {
        Some(
            div()
                .id("first-make-card")
                .px(px(24.))
                .py(px(10.))
                .rounded_md()
                .bg(theme::good())
                .text_color(theme::bg())
                .cursor_pointer()
                .hover(|s| s.opacity(0.9))
                .on_mouse_down(
                    MouseButton::Left,
                    cx.listener(|this, _ev, _w, cx| {
                        // Mint a real editable card (its substance their own home cell)
                        // and drop into the first-card view to press + edit it live.
                        this.make_first_card(cx);
                    }),
                )
                .child("make your first card — a thing that is yours  →")
                .into_any_element(),
        )
    }

    /// The non-card-pane stub: no authoring machinery, so the first-view shows no
    /// "make a card" invite (the calm landing is unchanged).
    #[cfg(not(all(feature = "dev-surfaces", feature = "card-pane")))]
    pub(crate) fn first_card_invite(&self, _cx: &mut Context<Self>) -> Option<gpui::AnyElement> {
        None
    }

    // === MAKE YOUR FIRST CARD — the onboarding keystone ==================
    // The path from "I'm in" to "I made a thing." A first-timer clicks one
    // affordance on the calm first-view; a real editable starter card is minted
    // over the LIVE World (its substance their own home cell), and the cockpit
    // shows the dedicated first-card view — the card live, two real edit
    // affordances (each a receipted patch), and the card's own +1 (a real turn).

    /// **MAKE YOUR FIRST CARD** — mint the onboarding starter card over the live
    /// `World` (its substance the stranger's own `home` = `user` anchor) and mount
    /// it. The first-view's "make your first card →" calls this; on success the
    /// cockpit shows [`Self::first_card_view`] (the dedicated onboarding surface).
    /// Re-entrant-safe: a second call while one is already minted is a no-op (the
    /// card is already theirs). Fail-soft: a build error is captured into
    /// `last_outcome`, leaving the first-view in place (never a dead-end).
    #[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
    pub fn make_first_card(&mut self, cx: &mut Context<Self>) {
        use starbridge_v2::dock::card_surface::build_first_card_surface;

        if self.first_card.is_some() {
            // Already minted — re-enter the first-card view (e.g. clicked twice).
            self.first_run = false;
            cx.notify();
            return;
        }
        // The stranger's OWN cell — their `user` anchor (the first-view calls it
        // "your home"). The card binds + fires on a cell they truly own.
        let home = self.anchors[2];
        // The attenuated operator hand the +1 fires + the view-edits mount under;
        // it satisfies the card's edit_authority, so a reshape-from-within is allowed.
        let held = dregg_cell::AuthRequired::Signature;
        let id = self.next_dev_surface_id();
        match build_first_card_surface(id, self.world.clone(), home, held, cx) {
            Ok(surface) => {
                let entity = surface.entity_handle();
                self.first_card = Some(super::FirstCardMount {
                    entity,
                    surface,
                    note: Some(
                        "minted — this card is yours (a fresh authored view over your home cell)."
                            .into(),
                    ),
                });
                // Leave the first-run welcome for the dedicated first-card view.
                self.first_run = false;
            }
            Err(e) => {
                self.last_outcome = Some(format!("could not make your first card: {e}"));
            }
        }
        cx.notify();
    }

    /// Onboarding edit #1: **add a button** to the first card — a real
    /// [`ViewPatch::AddButton`](deos_js::card_editor::ViewPatch) through the card's
    /// editable view document (a *receipted patch with blame*), re-folding the view
    /// and repainting the live [`CardPane`]. The new button fires the SAME `bump`
    /// affordance (so it is immediately live: another +1). Refused in-band if the
    /// operator's `held` does not satisfy the card's edit_authority.
    #[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
    pub fn first_card_add_button(&mut self, cx: &mut Context<Self>) {
        let patch = deos_js::card_editor::ViewPatch::AddButton {
            label: "+1 (you added this)".into(),
            turn: "bump".into(),
            arg: 1,
        };
        let note = match self.first_card.as_ref() {
            Some(mount) => match mount.surface.edit_view(patch, cx) {
                Ok(()) => Some(
                    "added a button — a receipted patch with blame; the card re-folded + \
                     repainted (the view is data, not a recompile)."
                        .to_string(),
                ),
                Err(e) => Some(format!("refused: {e}")),
            },
            None => None,
        };
        if let (Some(mount), Some(n)) = (self.first_card.as_mut(), note) {
            mount.note = Some(n);
        }
        cx.notify();
    }

    /// Onboarding edit #2: **rename the title** of the first card — a real
    /// [`ViewPatch::Relabel`](deos_js::card_editor::ViewPatch) (the keystone
    /// "change a label" gesture) through the editable view document, re-folding +
    /// repainting. Relabels the starter "my first card" title to a personalized one
    /// (idempotent: a second click is an in-band no-op, since the text already moved).
    #[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
    pub(crate) fn first_card_rename(&mut self, cx: &mut Context<Self>) {
        let patch = deos_js::card_editor::ViewPatch::Relabel {
            from: "my first card".into(),
            to: "★ my card (I named this)".into(),
        };
        let note = match self.first_card.as_ref() {
            Some(mount) => match mount.surface.edit_view(patch, cx) {
                Ok(()) => Some(
                    "renamed the title — another receipted patch; the change is accountable \
                     (blame attributes the new line to you)."
                        .to_string(),
                ),
                Err(e) => Some(format!("refused (already renamed?): {e}")),
            },
            None => None,
        };
        if let (Some(mount), Some(n)) = (self.first_card.as_mut(), note) {
            mount.note = Some(n);
        }
        cx.notify();
    }

    /// Onboarding fire: the first card's **+1** — fire its `bump` affordance =
    /// ONE cap-gated verified turn on the stranger's own home cell (a real receipt;
    /// the bound count advances on the next paint). This is the SAME turn the
    /// rendered card button fires; surfacing it as a labeled affordance lets the
    /// onboarding view note the receipt count so a first-timer SEES it land.
    #[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
    pub fn first_card_bump(&mut self, cx: &mut Context<Self>) {
        let note = match self.first_card.as_ref() {
            Some(mount) => {
                let res = mount.surface.applet().borrow_mut().fire("bump", 1);
                match res {
                    Ok(_receipt) => {
                        let n = mount.surface.receipt_count();
                        Some(format!(
                            "+1 fired — a real verified turn on your home cell (now {n} \
                             receipt{} on this card's tape).",
                            if n == 1 { "" } else { "s" }
                        ))
                    }
                    Err(e) => Some(format!("the +1 did not commit: {e}")),
                }
            }
            None => None,
        };
        if let (Some(mount), Some(n)) = (self.first_card.as_mut(), note) {
            mount.note = Some(n);
        }
        cx.notify();
    }

    /// Leave the dedicated first-card view for the full cockpit frame. The card
    /// STAYS minted on the ledger (it is theirs — they can re-find it); this only
    /// dismisses the onboarding surface so they meet the five modes.
    #[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
    pub(crate) fn leave_first_card(&mut self, cx: &mut Context<Self>) {
        self.first_card = None;
        self.first_run = false;
        cx.notify();
    }

    /// The first card's current view-source JSON (the editable document fold) — so the
    /// onboarding bake can assert a receipted edit landed IN the document (not just the
    /// rendered tree). `None` when no first card is mounted.
    #[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
    pub fn first_card_view_source(&self) -> Option<String> {
        self.first_card.as_ref().map(|m| m.surface.view_source())
    }

    /// The number of receipts on the first card's OWN live tape (genuine committed
    /// turns the card's `+1` fired) — so the onboarding bake can assert the +1 landed
    /// exactly once on this card (apart from the cockpit's own bookkeeping turns).
    /// `0` when no first card is mounted.
    #[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
    pub fn first_card_receipt_count(&self) -> usize {
        self.first_card
            .as_ref()
            .map(|m| m.surface.receipt_count())
            .unwrap_or(0)
    }

    /// THE FIRST-CARD VIEW — the dedicated onboarding surface a first-timer meets
    /// the instant they make their first card. The card LIVE (its `+1` fires a real
    /// turn, its bound count re-reads the ledger), two real **edit affordances**
    /// ("add a button" / "rename the title", each a *receipted patch with blame*
    /// that re-folds + repaints the card), a friendly note showing the last gesture
    /// landed, and a quiet "explore everything →" into the full frame. This is the
    /// closed loop: click → a card that is YOURS → press its button (a real turn) →
    /// edit it live (a receipted patch) → it re-renders. No internals needed.
    #[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
    pub(crate) fn first_card_view(&self, cx: &mut Context<Self>) -> gpui::AnyElement {
        let Some(mount) = self.first_card.as_ref() else {
            // No card mounted (shouldn't happen on this path) — fall back to the
            // calm first-view so the surface is never blank.
            return self.first_view(cx).into_any_element();
        };
        // Immediate-mode binds re-read the live ledger at render time, so a notify each
        // paint keeps the bound count current after a +1 lands (mirrors the mode cards).
        mount.entity.update(cx, |_card, cx| cx.notify());
        let entity = mount.entity.clone();
        let note = mount.note.clone();

        // The two edit affordances — each a real receipted patch through the card's
        // editable view document. GUARDED at the event boundary (the patch + entity
        // swap must never unwind to gpui's nounwind callback — the same discipline as
        // the mode-card edit control).
        let add_btn = Button::new(SharedString::from("first-card-add-button"))
            .label("✎ add a button")
            .ghost()
            .small()
            .on_click(cx.listener(|this, _ev: &ClickEvent, _w, cx| {
                Cockpit::guard_ui_event("first-card-add-button", || {
                    this.first_card_add_button(cx);
                });
            }));
        let rename_btn = Button::new(SharedString::from("first-card-rename"))
            .label("✎ rename the title")
            .ghost()
            .small()
            .on_click(cx.listener(|this, _ev: &ClickEvent, _w, cx| {
                Cockpit::guard_ui_event("first-card-rename", || {
                    this.first_card_rename(cx);
                });
            }));
        let bump_btn = Button::new(SharedString::from("first-card-bump"))
            .label("▶ press +1 (fire a real turn)")
            .small()
            .on_click(cx.listener(|this, _ev: &ClickEvent, _w, cx| {
                Cockpit::guard_ui_event("first-card-bump", || {
                    this.first_card_bump(cx);
                });
            }));

        div()
            .id("first-card-view")
            .size_full()
            .flex()
            .flex_col()
            .items_center()
            .justify_center()
            .gap_4()
            .bg(theme::bg())
            .text_color(theme::text())
            // The warm framing — "you made a thing."
            .child(
                div()
                    .flex()
                    .flex_col()
                    .items_center()
                    .gap_1()
                    .child(
                        div()
                            .text_xl()
                            .text_color(theme::accent())
                            .child("you made your first card"),
                    )
                    .child(
                        div()
                            .max_w(px(480.))
                            .text_sm()
                            .text_color(theme::muted())
                            .child(
                                "it's yours and it's live. press its +1 to fire a real \
                                 verified turn, or change it below — every edit is a \
                                 receipted patch, not a recompile.",
                            ),
                    ),
            )
            // THE LIVE CARD — the real CardPane over the live World (its bound count
            // re-reads the ledger; its rendered +1 fires a real turn).
            .child(
                div()
                    .w(px(480.))
                    .min_h(px(180.))
                    .p_2()
                    .border_1()
                    .border_color(theme::accent())
                    .rounded_md()
                    .bg(theme::panel())
                    .child(entity),
            )
            // THE ONBOARDING AFFORDANCES — fire + the two live edits.
            .child(
                div()
                    .flex()
                    .items_center()
                    .gap_2()
                    .child(bump_btn)
                    .child(add_btn)
                    .child(rename_btn),
            )
            // THE LAST-GESTURE NOTE — so a first-timer SEES their click did something
            // real (a receipt, a patch).
            .when_some(note, |el, n| {
                el.child(
                    div()
                        .max_w(px(480.))
                        .px_3()
                        .py_1p5()
                        .rounded_md()
                        .bg(theme::panel())
                        .text_xs()
                        .text_color(theme::good())
                        .child(SharedString::from(n)),
                )
            })
            // The quiet door to the full frame — the card stays theirs.
            .child(
                div()
                    .id("first-card-explore")
                    .text_xs()
                    .text_color(theme::muted())
                    .cursor_pointer()
                    .hover(|s| s.text_color(theme::accent()))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(|this, _ev, _w, cx| this.leave_first_card(cx)),
                    )
                    .child("explore everything →"),
            )
            .into_any_element()
    }

    // === THE TOP BAR =====================================================

    /// The persistent TOP BAR — the identity cell + its cap-badge, the live
    /// ledger clock (height + latest receipt), and the ⌘K palette summon. Calm,
    /// always-present (the chrome you learn once).
    pub(crate) fn top_bar(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let w = self.world.borrow();
        // Identity: the user anchor (the operator principal) + a cap-badge = how
        // many capabilities it holds in its c-list (its reach over the world).
        let user = self.anchors[2];
        let id_short = reflect::short_hex(user.as_bytes());
        let cap_count = w
            .ledger()
            .get(&user)
            .map(|c| c.capabilities.len())
            .unwrap_or(0);
        // The live ledger clock: height + the latest receipt hash (the world's
        // pulse — reuses the embedded executor's own head).
        let height = w.height();
        let latest = w
            .receipts()
            .last()
            .map(|r| reflect::short_hex(&r.receipt_hash()))
            .unwrap_or_else(|| "genesis".into());
        drop(w);

        div()
            .flex()
            .items_center()
            .gap_3()
            .px_3()
            .py_2()
            .w_full()
            .border_b_1()
            .border_color(theme::border())
            .bg(theme::panel())
            // Identity cell + cap-badge.
            .child(
                div()
                    .flex()
                    .items_center()
                    .gap_2()
                    .child(
                        div()
                            .text_color(theme::text())
                            .child(SharedString::from("Starbridge")),
                    )
                    .child(pill(format!("you · {id_short}"), theme::accent()))
                    .child(pill(format!("🔑 {cap_count} caps"), theme::good())),
            )
            // The live ledger clock (height + latest receipt).
            .child(
                div()
                    .flex()
                    .items_center()
                    .gap_2()
                    .child(pill(format!("⛓ h{height}"), theme::accent()))
                    .child(
                        div()
                            .text_xs()
                            .text_color(theme::muted())
                            .child(format!("◷ {latest}")),
                    ),
            )
            // The ⌘K palette summon (right-aligned). Clickable + a hint.
            .child(
                div()
                    .id("topbar-palette")
                    .ml_auto()
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(theme::panel_hi())
                    .border_1()
                    .border_color(theme::border())
                    .text_xs()
                    .text_color(theme::accent())
                    .cursor_pointer()
                    .hover(|s| s.bg(theme::border()))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(|this, _ev, _w, cx| {
                            this.palette.toggle();
                            cx.notify();
                        }),
                    )
                    .child("⌘K · find anything"),
            )
            // The ⌘J dock toggle.
            .child(
                div()
                    .id("topbar-dock")
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(theme::panel_hi())
                    .border_1()
                    .border_color(theme::border())
                    .text_xs()
                    .text_color(if self.dock_open {
                        theme::accent()
                    } else {
                        theme::muted()
                    })
                    .cursor_pointer()
                    .hover(|s| s.bg(theme::border()))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(|this, _ev, _w, cx| this.toggle_dock(cx)),
                    )
                    .child(if self.dock_open {
                        "⌘J · dock ▾"
                    } else {
                        "⌘J · dock ▸"
                    }),
            )
    }

    // === THE LEFT RAIL — the FIVE MODES ==================================

    /// The persistent LEFT RAIL of the FIVE MODES. One click switches the whole
    /// content pane's intent. The rail is the coherence (five rooms, not 20
    /// doors). The active mode is derived from the active surface's
    /// [`Tab::mode`], so a palette `Go<Surface>` also highlights the right mode.
    pub(crate) fn mode_rail(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let active = self.active_mode();
        let mut rail = div()
            .flex()
            .flex_col()
            .gap_1()
            .p_2()
            .w(px(132.))
            .h_full()
            .border_r_1()
            .border_color(theme::border())
            .bg(theme::panel());
        // READ THE LAYOUT CELL — the rail's mode order is the layout cell's
        // `mode_order()` (rung 3), NOT the hardcoded `CockpitMode::ALL`. A reshape that
        // reorders/adds modes re-renders the rail.
        for (i, m) in self.layout_mode_order().into_iter().enumerate() {
            let is_active = m == active;
            rail = rail.child(
                div()
                    .id(("mode-rail", i))
                    .flex()
                    .flex_col()
                    .gap_0p5()
                    .px_2()
                    .py_2()
                    .rounded_md()
                    .bg(if is_active {
                        theme::panel_hi()
                    } else {
                        theme::panel()
                    })
                    .border_1()
                    .border_color(if is_active {
                        theme::accent()
                    } else {
                        theme::panel()
                    })
                    .cursor_pointer()
                    .hover(|s| s.bg(theme::border()))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev, _w, cx| this.set_mode(m, cx)),
                    )
                    .child(
                        div()
                            .flex()
                            .items_center()
                            .gap_1()
                            .text_color(if is_active {
                                theme::accent()
                            } else {
                                theme::text()
                            })
                            .child(SharedString::from(format!("{} {}", m.glyph(), m.label()))),
                    )
                    .child(div().text_xs().text_color(theme::muted()).child(m.blurb())),
            );
        }
        rail
    }

    /// The active MODE = the mode of the active surface (so the rail highlight
    /// tracks `Go<Surface>` palette jumps + nav-history restores + sub-nav/rail
    /// clicks uniformly — there is no separate mode selector to keep in sync). READ
    /// from the layout cell ([`Self::layout_mode_of`], rung 3) so a reshape that moves
    /// a surface to another mode also moves where its rail highlight lands.
    pub(crate) fn active_mode(&self) -> CockpitMode {
        self.layout_mode_of(self.active_tab())
    }

    // === THE MODE SUB-NAV — the mode's surfaces ==========================

    /// The sub-nav strip for the active mode: one chip per surface re-homed under
    /// the mode (its primary first). A click switches the main pane to that
    /// surface (through [`Self::set_tab`], which keeps the mode in step).
    pub(crate) fn mode_subnav(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let mode = self.active_mode();
        let active_tab = self.active_tab();
        let mut row = div()
            .flex()
            .flex_wrap()
            .items_center()
            .gap_1()
            .px_2()
            .py_1()
            .border_b_1()
            .border_color(theme::border())
            .bg(theme::panel());
        row = row.child(
            div()
                .text_xs()
                .text_color(theme::muted())
                .pr_1()
                .child(SharedString::from(format!("{} ·", mode.label()))),
        );
        // READ THE LAYOUT CELL — the mode's sub-nav surfaces are the layout cell's
        // `surfaces_of(mode)` (rung 3, each label resolved → `Tab`), NOT the hardcoded
        // `CockpitMode::surfaces`. A reshape that moves a surface here re-renders the chip row.
        for (i, t) in self.layout_surfaces_of(mode).into_iter().enumerate() {
            let is_active = t == active_tab;
            row = row.child(
                div()
                    .id(("mode-subnav", i))
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(if is_active {
                        theme::panel_hi()
                    } else {
                        theme::panel()
                    })
                    .text_xs()
                    .text_color(if is_active {
                        theme::accent()
                    } else {
                        theme::muted()
                    })
                    .cursor_pointer()
                    .hover(|s| s.bg(theme::border()))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev, _w, cx| this.set_tab(t, cx)),
                    )
                    .child(t.label()),
            );
        }
        row
    }

    // === THE DEV DOCK — the collapsible bottom strip =====================

    /// The collapsible DEV DOCK (⌘J) — the dev workspace strip, available in ANY
    /// mode. It surfaces the Dev mode's IDE surfaces (terminal · editor · shell)
    /// as quick-jump chips, so code/PTY is always one keystroke away instead of a
    /// lost surface. Rendered only when [`Self::dock_open`]; the headless bake
    /// can capture it open or closed.
    pub(crate) fn dev_dock(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let active_tab = self.active_tab();
        let mut bar = div()
            .flex()
            .items_center()
            .flex_wrap()
            .gap_1()
            .px_3()
            .py_1p5()
            .w_full()
            .border_t_1()
            .border_color(theme::border())
            .bg(theme::panel())
            .child(
                div()
                    .text_xs()
                    .text_color(theme::accent())
                    .pr_2()
                    .child("⌨ dev dock ·"),
            );
        // The IDE surfaces as quick-jump chips (the persistent dev strip) — READ from
        // the layout cell's Dev-mode surfaces (rung 3), so a reshape that re-homes an
        // IDE surface is reflected in the dock too.
        for (i, t) in self
            .layout_surfaces_of(CockpitMode::Dev)
            .into_iter()
            .enumerate()
        {
            let is_active = t == active_tab;
            bar = bar.child(
                div()
                    .id(("dev-dock", i))
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(if is_active {
                        theme::panel_hi()
                    } else {
                        theme::panel()
                    })
                    .border_1()
                    .border_color(theme::border())
                    .text_xs()
                    .text_color(if is_active {
                        theme::accent()
                    } else {
                        theme::muted()
                    })
                    .cursor_pointer()
                    .hover(|s| s.bg(theme::border()))
                    .on_mouse_down(
                        MouseButton::Left,
                        cx.listener(move |this, _ev, _w, cx| this.set_tab(t, cx)),
                    )
                    .child(t.label()),
            );
        }
        bar
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_tab_has_a_mode() {
        // The re-framing is total: every surface is re-homed under exactly one
        // mode (no surface deleted, none orphaned). `Tab::mode` must resolve to a
        // mode whose `surfaces()` actually contains it (not the Inhabit fallback).
        for &t in Tab::ALL.iter() {
            let m = t.mode();
            assert!(
                m.surfaces().contains(&t),
                "{:?} is re-homed under {:?} but that mode does not list it",
                t,
                m
            );
        }
    }

    #[test]
    fn the_twenty_surfaces_partition_across_five_modes() {
        // Each Tab belongs to EXACTLY one mode (a partition, not an overlap).
        for &t in Tab::ALL.iter() {
            let homes: Vec<CockpitMode> = CockpitMode::ALL
                .into_iter()
                .filter(|m| m.surfaces().contains(&t))
                .collect();
            assert_eq!(
                homes.len(),
                1,
                "{:?} must belong to exactly one mode, found {:?}",
                t,
                homes
            );
        }
        // And the union covers every Tab (the modes' surfaces sum to ALL).
        let total: usize = CockpitMode::ALL.iter().map(|m| m.surfaces().len()).sum();
        assert_eq!(
            total,
            Tab::ALL.len(),
            "the five modes' surfaces must sum to exactly the full surface set"
        );
    }

    #[test]
    fn each_mode_has_a_primary_surface() {
        for m in CockpitMode::ALL {
            assert_eq!(
                m.primary(),
                m.surfaces()[0],
                "a mode's primary is its first surface"
            );
            assert_eq!(m.primary().mode(), m, "the primary belongs to its own mode");
        }
    }

    // RUNG-3 LABEL BRIDGE — the layout cell speaks in label STRINGS; the cockpit
    // resolves them back to enums. Every mode/surface label round-trips through its
    // inverse, so the read-wire (layout cell → rail) is lossless.
    #[test]
    fn every_mode_label_resolves_back_to_its_mode() {
        for m in CockpitMode::ALL {
            assert_eq!(
                CockpitMode::from_label(m.label()),
                Some(m),
                "{:?}'s label `{}` must resolve back to it",
                m,
                m.label()
            );
        }
        assert_eq!(
            CockpitMode::from_label("Nowhere"),
            None,
            "an unknown mode label resolves to None (the read degrades to the hardcoded ALL)"
        );
    }

    #[test]
    fn every_surface_label_resolves_back_to_its_tab() {
        // The layout cell's surface rows ARE `Tab::label()` strings (the layout card's
        // `cockpit_default` mirrors them); each must resolve back to its `Tab`.
        for &t in Tab::ALL.iter() {
            assert_eq!(
                Tab::from_label(t.label()),
                Some(t),
                "{:?}'s label `{}` must resolve back to it",
                t,
                t.label()
            );
        }
        assert_eq!(
            Tab::from_label("NO-SUCH-SURFACE"),
            None,
            "an unknown surface label resolves to None (the read skips it)"
        );
    }
}

/// **RUNG-3: THE COCKPIT'S RAIL IS DRIVEN BY THE LAYOUT CELL** — a real headless cockpit
/// over the demo world, rendered (so the rail/sub-navs READ the live layout card), then
/// reshaped from within (a surface moved to another mode) with the read-wire reflecting the
/// move on the re-render. Gated on `card-pane` (where the layout cell exists); the gpui-free
/// build keeps the hardcoded fallback (the pure tests above cover the bridge there).
///
/// Run: `cd starbridge-v2 && cargo test --features native-full --lib cockpit::frame::layout_cell_drives_the_rail -- --nocapture`
#[cfg(all(
    test,
    feature = "dev-surfaces",
    feature = "card-pane",
    feature = "render-capture"
))]
mod layout_cell_drives_the_rail {
    use super::*;
    use gpui::{AppContext, HeadlessAppContext, PlatformTextSystem, px, size};
    use gpui_wgpu::CosmicTextSystem;
    use std::borrow::Cow;
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::sync::Arc;

    /// The same headless gpui app the cockpit bake uses (fonts + kit + theme), so the
    /// cockpit's gpui-component widgets render without panicking.
    fn headless() -> HeadlessAppContext {
        static LILEX: &[u8] = include_bytes!("../../assets/fonts/Lilex-Regular.ttf");
        static IBM_PLEX: &[u8] = include_bytes!("../../assets/fonts/IBMPlexSans-Regular.ttf");
        let text_system: Arc<dyn PlatformTextSystem> =
            Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
        text_system
            .add_fonts(vec![Cow::Borrowed(LILEX), Cow::Borrowed(IBM_PLEX)])
            .expect("register headless fonts");
        let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
            gpui_platform::current_headless_renderer()
        });
        cx.update(|cx| gpui_component::init(cx));
        cx
    }

    #[test]
    fn layout_cell_drives_the_rail_and_a_reshape_moves_a_surface() {
        let mut cx = headless();
        let (world, anchors) = world::demo_world();
        let shared = Rc::new(RefCell::new(world));
        let window = cx
            .open_window(size(px(1280.), px(832.)), |window, cx| {
                let view = cx.new(|cx| {
                    let focus = cx.focus_handle();
                    Cockpit::with_node(shared.clone(), anchors, focus, None, None)
                });
                view.update(cx, |c, cx| c.focus_on_open(window, cx));
                view
            })
            .expect("open the cockpit window");
        let entity = window.root(&mut cx).expect("cockpit root entity");
        // FIRST DRAW — runs `render` → `ensure_layout_card` builds the layout cell, and
        // `mode_rail`/`mode_subnav` READ it (instead of the hardcoded `CockpitMode::surfaces`).
        cx.run_until_parked();
        cx.update_window(window.into(), |_, w, _| w.refresh())
            .expect("refresh the cockpit window");
        cx.run_until_parked();

        // (A) THE RAIL READS THE LAYOUT CELL — its mode order is the cell's `mode_order()`,
        // and matches the five modes (the default mirrors the hardcoded arrangement).
        let order = entity.read_with(&cx, |c, _| c.layout_mode_order());
        assert_eq!(
            order,
            CockpitMode::ALL.to_vec(),
            "the rail's mode order is READ from the layout cell (default = the five modes)"
        );
        // The Inhabit sub-nav reads the cell; AGENT lives in Operate by default.
        let inhabit_before =
            entity.read_with(&cx, |c, _| c.layout_surfaces_of(CockpitMode::Inhabit));
        assert!(
            !inhabit_before.contains(&Tab::Agent),
            "AGENT does not start in Inhabit's sub-nav (it lives in Operate)"
        );
        assert_eq!(
            entity.read_with(&cx, |c, _| c.layout_mode_of(Tab::Agent)),
            CockpitMode::Operate,
            "AGENT's rail highlight reads Operate from the layout cell"
        );

        // (B) RESHAPE FROM WITHIN — move AGENT to Inhabit (a `move:` affordance's effect),
        // a receipted cap-gated patch on the layout cell.
        entity.update(&mut cx, |c, cx| {
            c.reshape_layout_move(Tab::Agent, CockpitMode::Inhabit, cx)
        });
        // Re-render — the rail/sub-navs re-READ the reshaped cell (no panic on the redraw).
        cx.update_window(window.into(), |_, w, _| w.refresh())
            .expect("refresh after the reshape");
        cx.run_until_parked();

        // (C) THE READ-WIRE REFLECTS THE MOVE — the rail's Inhabit sub-nav now carries AGENT,
        // Operate no longer does, and AGENT's rail highlight reads Inhabit.
        let inhabit_after =
            entity.read_with(&cx, |c, _| c.layout_surfaces_of(CockpitMode::Inhabit));
        assert!(
            inhabit_after.contains(&Tab::Agent),
            "after the reshape AGENT is in Inhabit's sub-nav (the rail re-read the cell)"
        );
        assert!(
            !entity
                .read_with(&cx, |c, _| c.layout_surfaces_of(CockpitMode::Operate))
                .contains(&Tab::Agent),
            "AGENT left Operate's sub-nav (the surface MOVED, not duplicated)"
        );
        assert_eq!(
            entity.read_with(&cx, |c, _| c.layout_mode_of(Tab::Agent)),
            CockpitMode::Inhabit,
            "AGENT's rail highlight now reads Inhabit (the `Go<Surface>` jump follows the move)"
        );
        // The reshape left a real receipt on the layout cell's chain.
        let receipts = entity.read_with(&cx, |c, _| {
            c.layout_card
                .as_ref()
                .map(|lc| lc.card().receipt_count())
                .unwrap_or(0)
        });
        assert_eq!(
            receipts, 1,
            "the reshape committed exactly one provenance receipt"
        );

        println!(
            "OK rung-3: the cockpit rail is DRIVEN BY THE LAYOUT CELL — default mirrored the \
             five modes, and a from-within reshape moved AGENT Operate→Inhabit (receipted), \
             which the rail/sub-nav read-wire reflected on the re-render."
        );
    }
}
