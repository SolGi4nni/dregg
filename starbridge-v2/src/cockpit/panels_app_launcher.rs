//! THE PRE-BUILT APP LAUNCHER — the cockpit surface that makes the wired
//! starbridge-apps (gallery / sealed-auction / bounty-board / escrow-market /
//! subscription / nameservice / compute-exchange / privacy-voting / identity /
//! governed-namespace / supply-chain-provenance / tool-access-delegation /
//! swarm-orchestration / agent-provenance / compartment-workflow-mandate /
//! storage-gateway-mandate / agent-orchestration / polis / …) LAUNCHABLE +
//! INTERACTIVE from within the live desktop.
//!
//! The infrastructure already exists ([`crate::app_registry::AppRegistry`] +
//! [`starbridge_v2::powerbox::RegistryLauncher`], both built + tested): the registry
//! lists each app (id · name · what-it-does) and `launch_on_world` seeds an app's
//! cell + program onto the cockpit's LIVE [`World`](crate::world::World) and commits
//! its representative affordance as a REAL verified turn through the embedded
//! executor. This module is the missing UI: it renders the launcher rows as a
//! section of the POWERBOX/LAUNCHER surface (each a "launch" button), and on a launch
//! it drives [`RegistryLauncher::launch_on_world`] so the app's cell + receipt land on
//! `World::ledger()` / `World::receipts()` — the SAME ledger the cockpit's cell
//! inspector reads. So launching gallery mounts gallery's cell on your world, fires
//! gallery's `submit` verified turn, and the cell is immediately inspectable
//! (clickable → OBJECTS / INSPECTOR).
//!
//! Gated on `app-registry` (the feature that pulls the pre-built starbridge-apps into
//! the cockpit). The launch + the real verified turn run on the cockpit's own World.

#![cfg(feature = "app-registry")]

use super::*;

use starbridge_v2::powerbox::RegistryLauncher;

/// The federation the launcher births app substrates into (the app cipherclerk is a
/// fresh random identity per launch, so re-launching never collides — each press
/// births a distinct app instance on the live world).
const APPS_FEDERATION: [u8; 32] = [0x5Eu8; 32];

/// One **pre-built app launched onto the cockpit's LIVE World** — a real app cell
/// seeded onto the live ledger, its representative affordance fired as a real
/// verified turn. The cell is on `World::ledger()` (inspectable). Held by the cockpit
/// so the launcher surface can render the roster + let each be clicked to inspect.
#[derive(Clone)]
pub(crate) struct LaunchedAppRecord {
    /// The registry id of the app launched (e.g. `"gallery"`).
    pub id: String,
    /// The display name shown in the roster.
    pub name: String,
    /// The launched app's primary cell on the live World ledger (the inspector pointer).
    pub cell: CellId,
}

impl Cockpit {
    /// **The pre-built app launcher section** — one row per wired starbridge-app
    /// ([`RegistryLauncher::rows`]): its name + what-it-does + a "launch" button that
    /// mounts the app onto the live World and fires its representative verified turn.
    /// Plus the roster of already-launched apps (each a live cell, clickable to
    /// inspect). Rendered as a section of the POWERBOX/LAUNCHER surface.
    pub(crate) fn apps_launcher_section(&self, cx: &mut Context<Self>) -> impl IntoElement {
        let launcher = RegistryLauncher::standard(APPS_FEDERATION);
        let rows = launcher.rows();
        let launched = self.apps_launched.clone();

        let mut col = div().flex().flex_col().gap_1().mt_3();
        col = col.child(
            section_title(format!(
                "LAUNCH A PRE-BUILT APP · {} wired starbridge-app(s)",
                rows.len()
            ))
            .mb_1(),
        );
        col = col.child(div().text_xs().text_color(theme::muted()).child(
            "Each is a fully-built deos app (cells × cap-gated affordances). LAUNCH seeds its \
             cell + program onto your LIVE World and fires its representative VERIFIED turn \
             through the real executor — the cell + receipt land on your own ledger (click a \
             launched app below, or open OBJECTS / INSPECTOR, to inspect it). Launch again to \
             fire another real verified turn on a fresh instance.",
        ));

        // The last launch outcome banner (the executor's verdict — a real committed
        // receipt, or the in-band launch refusal).
        if let Some(banner) = &self.apps_outcome {
            let good = banner.starts_with("launched");
            col = col.child(
                div()
                    .mt_1()
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(theme::panel_hi())
                    .text_xs()
                    .text_color(if good { theme::good() } else { theme::warn() })
                    .child(banner.clone()),
            );
        }

        // ── one row per wired app: name · what-it-does · launch ──
        for r in &rows {
            let id = r.id.clone();
            let name = r.name.clone();
            let instances = launched.iter().filter(|a| a.id == r.id).count();
            let id_for_btn = id.clone();
            let name_for_btn = name.clone();
            col = col.child(
                div()
                    .flex()
                    .justify_between()
                    .items_center()
                    .gap_2()
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(theme::panel())
                    .border_1()
                    .border_color(theme::border())
                    .child(
                        div()
                            .flex()
                            .flex_col()
                            .child(
                                div()
                                    .text_xs()
                                    .text_color(theme::text())
                                    .child(format!("{} ({})", name, r.id)),
                            )
                            .child(
                                div()
                                    .text_xs()
                                    .text_color(theme::muted())
                                    .child(r.description.clone()),
                            ),
                    )
                    .child(
                        div()
                            .flex()
                            .items_center()
                            .gap_1()
                            .when(instances > 0, |d| {
                                d.child(pill(format!("{instances} launched"), theme::good()))
                            })
                            .child(
                                Button::new(SharedString::from(format!("launch-app-{}", r.id)))
                                    .label(if instances > 0 {
                                        "launch ↻"
                                    } else {
                                        "launch"
                                    })
                                    .primary()
                                    .xsmall()
                                    .on_click(cx.listener(
                                        move |this, _ev: &ClickEvent, window, cx| {
                                            this.run_launch_registry_app(
                                                id_for_btn.clone(),
                                                name_for_btn.clone(),
                                                window,
                                                cx,
                                            );
                                        },
                                    )),
                            ),
                    ),
            );
        }

        // ── the roster of launched apps (each a live cell on your World — click to inspect) ──
        if !launched.is_empty() {
            col = col.child(
                section_title(format!(
                    "{} app(s) launched · live on your World (click to inspect)",
                    launched.len()
                ))
                .mt_2()
                .mb_1(),
            );
            for a in &launched {
                let cell = a.cell;
                col = col.child(
                    div()
                        .id(SharedString::from(format!(
                            "launched-app-{}",
                            reflect::short_hex(&cell.0)
                        )))
                        .flex()
                        .justify_between()
                        .items_center()
                        .px_2()
                        .py_0p5()
                        .rounded_md()
                        .bg(theme::panel())
                        .cursor_pointer()
                        .hover(|s| s.bg(theme::panel_hi()))
                        .on_mouse_down(
                            MouseButton::Left,
                            cx.listener(move |this, _ev, _w, cx| {
                                // Focus the launched app's cell in the inspector + jump to
                                // the OBJECTS surface (the cell roster + reflective inspector).
                                this.selection = Selection::Cell(cell);
                                this.tab = Tab::Objects;
                                cx.notify();
                            }),
                        )
                        .child(div().text_xs().text_color(theme::text()).child(format!(
                            "{} · {}",
                            a.name,
                            reflect::short_hex(&cell.0)
                        )))
                        .child(
                            div()
                                .text_xs()
                                .text_color(theme::accent())
                                .child("inspect →"),
                        ),
                );
            }
        }

        // ── THE GADGET ROLODEX — the guest partition, LIVE in the cockpit ──
        // The SAME `guest::acquired_gadgets` read the guest bake renders (there
        // with no session — all discoverable), here over the LIVE session + the
        // launched designations recorded above: a launched-and-picked-up gadget
        // renders HELD (its cap is genuinely in the session c-list); the rest of
        // the catalog renders discoverable — never silently equal.
        #[cfg(all(feature = "gpui-ui", feature = "dev-surfaces"))]
        {
            let designations: Vec<(&str, CellId)> =
                launched.iter().map(|a| (a.id.as_str(), a.cell)).collect();
            let world = self.world.borrow();
            let gadgets = starbridge_v2::guest::acquired_gadgets(
                self.session.as_ref().map(|s| (s, &*world)),
                &designations,
            );
            let held_count = gadgets.iter().filter(|g| g.held()).count();
            col = col.child(
                section_title(format!(
                    "YOUR GADGETS · the rolodex — {held_count} held · {} discoverable",
                    gadgets.len() - held_count
                ))
                .mt_2()
                .mb_1(),
            );
            col = col.child(div().text_xs().text_color(theme::muted()).child(
                if self.session.is_some() {
                    "held = the gadget's cap is in YOUR session c-list (a launch picks it up \
                     via a real grant turn) · dimmed = catalog only, not held"
                } else {
                    "no live session — every gadget renders honestly as discoverable \
                     (possession is the c-list's to grant, never the catalog's)"
                },
            ));
            for g in &gadgets {
                let held = g.held();
                let name_color = if held { theme::text() } else { theme::muted() };
                let mut row = div()
                    .flex()
                    .items_center()
                    .gap_2()
                    .px_2()
                    .py_0p5()
                    .rounded_md()
                    .bg(theme::panel())
                    .child(div().text_xs().text_color(name_color).child(g.glyph))
                    .child(div().text_xs().text_color(name_color).child(g.name.clone()));
                row = if held {
                    row.child(pill("held", theme::good()))
                } else {
                    row.child(
                        div()
                            .text_xs()
                            .text_color(theme::muted())
                            .child("· not held"),
                    )
                };
                col = col.child(row);
            }
        }

        col
    }

    /// **LAUNCH a pre-built app onto the cockpit's LIVE World** — drive
    /// [`RegistryLauncher::launch_on_world`]: seed the app `id`'s cell + program onto
    /// the live world and commit its representative affordance as a REAL verified turn
    /// through the embedded executor. The app's cell + receipt land on `World::ledger()`
    /// / `World::receipts()` (the cockpit inspector path); the launched cell becomes the
    /// inspector's focus + is recorded in the launched-apps roster. Re-runnable: each
    /// press births a distinct app instance (a fresh random app identity), so a launch
    /// always fires a NEW real verified turn.
    pub(crate) fn run_launch_registry_app(
        &mut self,
        id: String,
        name: String,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) {
        let world = Rc::clone(&self.world);
        let result = RegistryLauncher::standard(APPS_FEDERATION).launch_on_world(&id, world);
        match result {
            Some(Ok(launched)) => {
                let cell = launched.primary_cell();
                let rhex = reflect::short_hex(&launched.receipt.receipt_hash());
                let actions = launched.receipt.action_count;
                // THE ROLODEX DESIGNATION — record `(registry_id, primary_cell)`;
                // the launcher's gadget rolodex partitions possession over exactly
                // these designations + the live session.
                self.apps_launched.push(LaunchedAppRecord {
                    id: id.clone(),
                    name: name.clone(),
                    cell,
                });
                // THE PICK-UP — with a LIVE session, designate the launched gadget
                // into the session root's c-list via one real verified grant turn
                // (`pick_up_gadget`), so `Session::reaches` — and the rolodex's
                // Held partition — genuinely flips. Fail-closed: a refusal is
                // surfaced in the banner and the gadget stays Discoverable.
                let picked_up = match self.session.as_ref().map(|s| s.root_cell) {
                    Some(root) => {
                        let outcome = starbridge_v2::app_registry::pick_up_gadget(
                            &mut self.world.borrow_mut(),
                            root,
                            cell,
                        );
                        match outcome {
                            Ok(_) => " Picked up: its cap is now in your session c-list \
                                      (the rolodex shows it HELD)."
                                .to_string(),
                            Err(e) => format!(" Pick-up refused (rolodex stays not-held): {e}"),
                        }
                    }
                    None => String::new(),
                };
                self.selection = Selection::Cell(cell);
                let has_card = self.has_live_card(&id);
                self.apps_outcome = Some(format!(
                    "launched {name}: cell {} on your live World — fired its representative \
                     verified turn (receipt {rhex}, {actions} action(s)). {}{} Inspect it in \
                     OBJECTS / INSPECTOR.",
                    reflect::short_hex(&cell.0),
                    if has_card {
                        "Its live CARD opened in a dock pane (its buttons fire real verified turns)."
                    } else {
                        ""
                    },
                    picked_up
                ));
                // FULL VIEW MOUNTING: open the app's BESPOKE deos-view card as a live dock
                // surface, bound to the just-launched cell on the live World — so the app
                // shows its OWN card UI and its buttons fire the app's real verified turns.
                // Additive: an app without a wired card keeps only the inspect behavior.
                #[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
                self.mount_launched_app_card(&id, &name, launched, window, cx);
                #[cfg(not(all(feature = "dev-surfaces", feature = "card-pane")))]
                let _ = (window, launched);
            }
            Some(Err(e)) => {
                self.apps_outcome = Some(format!("launch {id} refused: {e}"));
            }
            None => {
                self.apps_outcome = Some(format!("no wired app with id '{id}'"));
            }
        }
        self.refresh_cells();
        cx.notify();
    }

    /// Whether the app with `id` ships a bespoke card wired for live firing (so the
    /// launcher can tell the operator their launch opened a clickable card pane).
    fn has_live_card(&self, id: &str) -> bool {
        #[cfg(feature = "embedded-executor")]
        {
            starbridge_v2::app_registry::app_card(id).is_some()
        }
        #[cfg(not(feature = "embedded-executor"))]
        {
            let _ = id;
            false
        }
    }

    /// **Mount a launched app's bespoke card as a live dock pane** — the full-view-mount
    /// keystone. Builds an [`AppCardSurface`](starbridge_v2::dock::card_surface::AppCardSurface)
    /// over the just-launched [`LaunchedOnWorld`](starbridge_v2::app_registry::LaunchedOnWorld)
    /// (no relaunch — the SAME cell already on the live World) and grafts it beside the
    /// active pane (the editor/terminal/card dev-pane machinery). The card's buttons fire
    /// the app's REAL cap-gated verified turns through its spine. Fail-soft: an app without
    /// a wired card (or a parse failure) leaves the launch's inspect behavior untouched.
    #[cfg(all(feature = "dev-surfaces", feature = "card-pane"))]
    fn mount_launched_app_card(
        &mut self,
        app_id: &str,
        app_name: &str,
        launched: starbridge_v2::app_registry::LaunchedOnWorld,
        window: &mut Window,
        cx: &mut Context<Self>,
    ) {
        use starbridge_v2::dock::card_surface::build_app_card_surface;
        use starbridge_v2::dock::surface::CockpitSurface;

        let surface_id = self.next_dev_surface_id();
        match build_app_card_surface(surface_id, app_id, app_name, launched, cx) {
            Ok(surface) => {
                let boxed: Box<dyn CockpitSurface> = Box::new(surface);
                self.graft_dev_pane(boxed, window, cx);
            }
            Err(e) => {
                // No wired card / parse failure — the launch's inspect behavior stands.
                eprintln!("app-launcher: no live card surface for '{app_id}': {e}");
            }
        }
    }
}
