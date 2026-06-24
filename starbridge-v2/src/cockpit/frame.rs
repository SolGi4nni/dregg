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
    /// Switch the active MODE (a rail click) — opens the mode's primary surface
    /// (which moves the witnessed tab via [`Self::set_tab`]). The rail highlight
    /// then derives from the surface's [`Tab::mode`] ([`Self::active_mode`]), so
    /// there is no separate mode state to drift.
    pub(crate) fn set_mode(&mut self, mode: CockpitMode, cx: &mut Context<Self>) {
        self.set_tab(mode.primary(), cx);
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
        for (i, m) in CockpitMode::ALL.into_iter().enumerate() {
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
    /// clicks uniformly — there is no separate mode selector to keep in sync).
    pub(crate) fn active_mode(&self) -> CockpitMode {
        self.active_tab().mode()
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
        for (i, &t) in mode.surfaces().iter().enumerate() {
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
        // The IDE surfaces as quick-jump chips (the persistent dev strip).
        for (i, &t) in CockpitMode::Dev.surfaces().iter().enumerate() {
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
}
