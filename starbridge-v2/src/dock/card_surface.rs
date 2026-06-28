//! Mount a hyperdreggmedia CARD as a [`CockpitSurface`] — the keystone joy-path
//! weld. A [`crate::card_pane::CardPane`] (a real gpui `Render` over the cockpit's
//! LIVE `World`) hosted as a dock pane, exactly like the editor/terminal/agent
//! dev panes ([`super::editor_surface`], [`super::terminal_surface`]).
//!
//! Where the editor pane edits sovereign cells (a save = a `SetField` turn) and
//! the terminal pane runs a PTY, THIS pane renders a deos-js applet's `deos.ui.*`
//! view-tree into real gpui-component widgets bound to the live ledger: a `bind`
//! re-reads the operator's real cell off the live `World`, and a `+1` button fires
//! ONE cap-gated verified turn through `World::commit_turn` — a receipt the
//! cockpit's own cell inspector immediately sees (the SAME ledger the editor pane
//! saves onto). A child clicks the +1 and the count rises; the turn it fired
//! bottoms out in the verified executor, inheriting light-client unfoolability for
//! free.
//!
//! The card was BAKED (proven to pixels by the `--render-card-pane` PNG bake,
//! `main.rs::render_card_pane_headless`) but never grafted into the windowed dock;
//! this surface is the dock-mount that makes it CLICKABLE. The build path is
//! identical to the bake's: author the view-tree in real SpiderMonkey over an
//! applet ATTACHED to the live `World`, then host the resulting `CardPane` entity.
//!
//! Gated on `card-pane` (pulls `deos-view`'s gpui renderer + `agent-js`/deos-js)
//! AND `dev-surfaces` (the `graft_dev_pane` mount machinery) — the combination the
//! `open_card_pane` call site needs.

use std::cell::RefCell;
use std::rc::Rc;

use gpui::{
    div, AnyElement, App, AppContext, Context, Entity, FocusHandle, IntoElement, ParentElement,
    SharedString, Styled, Window,
};

use deos_view::ViewNode;
use dregg_cell::{AuthRequired, CellId};

use deos_js::card_editor::{CardEditor, ViewPatch};
use deos_js::portable::{AppletManifest, PortableApplet};
use deos_js::{Author, ViewTree};

use crate::agent_attach::{attach_agent, WorldSinkAdapter, AGENT_COUNTER_SLOT};
use crate::card_pane::{build_card_over_live, CardPane, SharedAttached};
use crate::world::World;

#[cfg(feature = "app-registry")]
use crate::card_pane::CardSubstanceRef;

use super::surface::{CockpitSurface, SurfaceId};

/// The card's authoring JS: a `deos.ui.*` view-tree — a title, a `bind` re-reading
/// the live cell's counter slot, and a `+1` button firing the `bump` affordance.
/// The build commits NO turn (it only stashes the view-tree into ephemeral
/// view-state); only the rendered button's later `fire` does. Mirrors the bake's
/// card_js (`main.rs::render_card_pane_headless`) so the dock card and the proven
/// PNG card are the SAME card.
fn card_authoring_js(view_key: &str) -> String {
    format!(
        r#"
        var app = deos.applet({{ affordances: ["bump"] }});
        var b = deos.ui.bind(function() {{ return app.get({slot}); }});
        b.props.slot = {slot};
        b.props.label = "live count: ";
        var tree = deos.ui.vstack(
            deos.ui.text("Counter card (live cockpit cell)"),
            b,
            deos.ui.button("+1", "bump", 1)
        );
        app.view.set("{key}", JSON.stringify(tree));
        0;
    "#,
        slot = AGENT_COUNTER_SLOT,
        key = view_key,
    )
}

/// Author a card over the cockpit's LIVE `World` and build a hostable
/// [`CardSurface`]. The flow is byte-for-byte the bake's
/// (`main.rs::render_card_pane_headless`): attach a counter applet to the live
/// World through the [`WorldSinkAdapter::live`] weld (so the card's substance is
/// `agent`'s REAL cell, the fire bounded by `held`), author the `deos.ui.*` tree
/// in real SpiderMonkey (commits NO turn), and host the resulting [`CardPane`] as a
/// gpui entity. The button's `on_click` then fires `bump` = one cap-gated verified
/// turn on the live ledger.
///
/// `rt` is a booted SpiderMonkey runtime passed in by the caller (the engine is a
/// process-global singleton; the call site owns its boot). A build error is
/// returned for the caller to surface fail-soft.
#[allow(clippy::result_large_err)]
pub fn build_card_surface(
    id: u64,
    rt: &mut deos_js::JsRuntime,
    world: Rc<RefCell<World>>,
    agent: CellId,
    cx: &mut App,
) -> Result<CardSurface, String> {
    // The card's affordance surface: `bump` (Signature — held, admitted). The cap
    // tooth in deos-js checks every fire against `held` before it reaches the
    // executor (the live World's executor is the second gate).
    let held = AuthRequired::Signature;
    let affordances = vec![("bump".to_string(), AuthRequired::Signature)];

    // Attach a counter applet to the LIVE cockpit World — the card's substance is
    // `agent`'s real cell; a fire lands on the ledger the inspector reads.
    let sink = WorldSinkAdapter::live(world);
    let attached = attach_agent(sink, agent, held, affordances);

    // Author the view-tree over the live applet (real SpiderMonkey, NO turn).
    let view_key = crate::card_pane::view_tree_key_for_card();
    let js = card_authoring_js(view_key);
    let (attached, tree): (_, ViewNode) = build_card_over_live(rt, attached, &js)?;

    // Share the live attached applet so the rendered button + the bind both drive
    // the SAME sovereign cell on the live ledger.
    let shared: SharedAttached = Rc::new(RefCell::new(attached));

    let pane_applet = shared.clone();
    let pane_tree = tree.clone();
    let entity =
        cx.new(|_cx| CardPane::new(pane_applet, pane_tree, "hyperdreggmedia · counter card"));

    Ok(CardSurface {
        id: SurfaceId(id),
        entity,
        applet: shared,
        focus: cx.focus_handle(),
    })
}

/// **Build the REFLECTIVE INSPECTOR card over the cockpit's LIVE World** — the
/// rung-2 mount. Where [`build_card_surface`] hosts a hand-authored counter card,
/// this hosts the [`deos_js::inspector_card`] card: a view-tree GENERATED IN RUST
/// from `focus`'s moldable faces (RawFields rows → live `Bind`s + labeled `Text`,
/// Affordances → cap-gated `Button`s), rendered by the SAME [`CardPane`] over the
/// SAME live attached applet. So the cockpit's Inspect-mode surface IS a deos-js
/// card: the focused cell's faces render live off the operator's real ledger, an
/// affordance button fires ONE cap-gated verified turn on the live `World`, and a
/// bound field row re-reads the advanced value on the next paint.
///
/// No SpiderMonkey is needed — the inspector view-tree is a pure function of the
/// faces ([`deos_js::inspector_card::inspector_view_over_attached`]), built directly
/// in Rust, then converted to the renderer's [`ViewNode`] through the canonical JSON
/// bridge ([`deos_view::parse_view_tree`] of [`deos_js::card_editor::ViewTree::to_json`]).
///
/// `held` is the operator's authority the affordance fires are mounted under (the
/// cap tooth checks every fire against it). A build error is returned for the caller
/// to surface fail-soft (the cockpit keeps the Rust moldable inspector as fallback).
///
/// ## Edit-from-within: the open seam
///
/// This rung mounts the inspector card LIVE (render + fire on the cockpit's World).
/// The reshape-the-inspector-from-within keystone
/// ([`deos_js::inspector_card::InspectorCard::edit_view`] — a `ViewPatch` that
/// re-folds the view + leaves a receipted patch with blame) is PROVEN at rung 1 over
/// the embedded engine but NOT yet routed through this live mount: [`CardPane`] holds
/// the generated [`ViewNode`] as a static render input with no patch entry. Wiring it
/// is additive (hold the view as an editable [`deos_js::card_editor::ViewTree`]
/// document on the mount, apply a `ViewPatch`, and rebuild the `CardPane` from the
/// re-folded tree) and is the next rung — the view is already DATA, not compiled code,
/// so the reshape needs a route, not a recompile.
#[allow(clippy::result_large_err)]
pub fn build_inspector_card_surface(
    id: u64,
    world: Rc<RefCell<World>>,
    focus: CellId,
    held: AuthRequired,
    cx: &mut App,
) -> Result<CardSurface, String> {
    // The inspector's affordance surface over the focused cell: `bump` (Signature —
    // held, admitted) advances a state slot so a fired button visibly moves a bound
    // row, and `escalate` (Proof — an OVER-REACH the operator's Signature does not
    // satisfy) is present so the cap tooth is genuinely exercised: it is REFUSED
    // in-band and the reflective `project_for(held)` never even surfaces it as a
    // button. The fire commits THROUGH `World::commit_turn` onto the live ledger.
    let affordances = vec![
        ("bump".to_string(), AuthRequired::Signature),
        ("escalate".to_string(), AuthRequired::Proof),
    ];

    // Attach an applet to the LIVE cockpit World, focused on `focus` — the card's
    // substance is the operator's REAL cell; a fire lands on the ledger the inspector
    // reads. (The counter slot the bump writes is `AGENT_COUNTER_SLOT`.)
    let sink = WorldSinkAdapter::live(world);
    let attached = attach_agent(sink, focus, held.clone(), affordances);

    // GENERATE the inspector view-tree IN RUST from the focused cell's live faces
    // (RawFields + the cap-gated affordances `held` may fire), then bridge it into
    // the renderer's `ViewNode` through the canonical JSON shape both sides share.
    let inspector_tree = deos_js::inspector_card::inspector_view_over_attached(&attached, &held);
    let tree: ViewNode = deos_view::parse_view_tree(&inspector_tree.to_json())
        .map_err(|e| format!("inspector view-tree bridge: {e}"))?;

    // Share the live attached applet so the rendered buttons + the binds both drive
    // the SAME sovereign cell on the live ledger.
    let shared: SharedAttached = Rc::new(RefCell::new(attached));

    let pane_applet = shared.clone();
    let pane_tree = tree.clone();
    let entity = cx.new(|_cx| {
        CardPane::new(
            pane_applet,
            pane_tree,
            "inspector · live cell (deos-js card)",
        )
    });

    Ok(CardSurface {
        id: SurfaceId(id),
        entity,
        applet: shared,
        focus: cx.focus_handle(),
    })
}

/// A dock-hostable wrapper around a [`CardPane`] gpui entity — a hyperdreggmedia
/// card as a live cockpit surface. Holds the shared live applet handle so the host
/// can read the live receipt count after a button fires (the SAME applet the
/// rendered widgets drive).
pub struct CardSurface {
    id: SurfaceId,
    entity: Entity<CardPane>,
    applet: SharedAttached,
    focus: FocusHandle,
}

impl CardSurface {
    /// The shared live applet handle (so the host/test can read the live ledger /
    /// receipt count after a button fire — the SAME applet the card drives).
    pub fn applet(&self) -> SharedAttached {
        self.applet.clone()
    }

    /// The on-ledger receipt count on the card's live tape (genuine `TurnReceipt`s
    /// committed by the card's button) — the honest "N fires" truth.
    pub fn receipt_count(&self) -> usize {
        self.applet.borrow().receipt_count()
    }

    /// The [`CardPane`] gpui entity handle (for a host that mounts the card's body
    /// directly as a panel child rather than wrapping it in the dock surface — the
    /// inspector-card-as-Inspect-surface mount).
    pub fn entity_handle(&self) -> Entity<CardPane> {
        self.entity.clone()
    }
}

impl CockpitSurface for CardSurface {
    fn item_id(&self) -> SurfaceId {
        self.id
    }

    fn tab_label(&self) -> SharedString {
        SharedString::from("card")
    }

    fn render_body(&mut self, _window: &mut Window, cx: &mut App) -> AnyElement {
        // The card's `bind` re-reads the live ledger at RENDER time (immediate
        // mode), so a notify on the card entity each frame keeps the bound count
        // current after a fire (the cockpit repaints on its dynamics cadence; this
        // makes the card track the live cell even if the fire's own closure does
        // not notify). Then host the entity as the body.
        self.entity.update(cx, |_card, cx| cx.notify());
        div()
            .size_full()
            .child(self.entity.clone())
            .into_any_element()
    }

    fn focus_handle(&self, _cx: &App) -> FocusHandle {
        self.focus.clone()
    }

    fn boxed_clone(&self) -> Box<dyn CockpitSurface> {
        // A split clones the surface into the new pane: share the SAME live entity
        // + applet (a thin handle onto the shared `World`), so both panes drive the
        // SAME sovereign cell — the card is one live object, mirrored.
        Box::new(CardSurface {
            id: self.id,
            entity: self.entity.clone(),
            applet: self.applet.clone(),
            focus: self.focus.clone(),
        })
    }
}

// ===========================================================================
// THE LANDED CARDS AS THEIR MODE'S MAIN-PANE SURFACE — the same
// CardPane-over-live-World pattern as the inspector card, now generalized to
// the reflective cards (composer / objects / graph / dynamics / agent /
// links / inspector). Each generates its view-tree IN RUST from the live ledger
// (the card's own public view-builder), bridges it to a `ViewNode`, and hosts it as
// a `CardPane` over an applet ATTACHED to the cockpit's live World — so a bound
// row re-reads the operator's real cell and an affordance button fires ONE
// cap-gated verified turn on that World.
//
// AND each mount holds its view as an editable `ViewTree` document (adopted by
// a `CardEditor`), so a `ViewPatch` (deos.editor/edit_view) re-folds the view +
// rebuilds the `CardPane` — the surface is reshaped LIVE from within (the view
// is data, not compiled code; the reshape is a receipted patch, not a recompile).
// ===========================================================================

/// Which landed card a [`ModeCardSurface`] mounts — the deos-js card that IS a given
/// cockpit mode's main-pane surface. Each names a `deos_js::*_card` whose view-tree is a
/// pure function of the live ledger (plus a focus, for the links card).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ModeCard {
    /// AUTHOR · the composition composer (`deos_js::composer_card`).
    Composer,
    /// INHABIT · the object roster (`deos_js::objects_card`).
    Objects,
    /// INHABIT · the ocap graph (`deos_js::graph_card`).
    Graph,
    /// INHABIT/DEV · the live dynamics feed (`deos_js::dynamics_card`).
    Dynamics,
    /// OPERATE · the agent-activity card (`deos_js::agent_card`).
    Agent,
    /// AUTHOR · what-links-here (`deos_js::links_card`).
    Links,
    /// INHABIT · the proof-attach + STARK verification-status board (`deos_js::proofs_card`).
    /// A whole-image survey (not per-cell): a summary pill row + one section per committed
    /// turn. Read-only (it never mints a STARK in a paint — the honest stance).
    Proofs,
    /// INHABIT · live organ cell-state (`deos_js::organs_card`). A whole-image survey:
    /// trustlines · flash wells · remote-path, each a section. Read-only.
    Organs,
    /// HOME · the warm landing portal / boot view (`deos_js::home_card`). A whole-image
    /// reflection: the masthead (liveness pills) + a section per portal section. Read-only.
    Home,
    /// INSPECT · the focused cell's reflected state + its cap-gated affordances
    /// (`deos_js::inspector_card`). The INSPECT-ACT surface reborn as card data: the
    /// RawFields face → live `Bind` rows + labeled `Text`, the Affordances face →
    /// cap-gated `Button`s that fire a real verified turn. This routes the Inspect-Act
    /// surface through the SAME generalized mode-card mount as the other reflective cards
    /// (so it gets the live-World bind + the edit-from-within seam for free), rather than
    /// the hardcoded gpui `inspect_act_panel` tree.
    Inspector,
}

impl ModeCard {
    /// A short surface title (the card frame chrome).
    pub fn title(self) -> &'static str {
        match self {
            ModeCard::Composer => "composer · live composition (deos-js card)",
            ModeCard::Objects => "objects · live cell roster (deos-js card)",
            ModeCard::Graph => "graph · live ocap web (deos-js card)",
            ModeCard::Dynamics => "dynamics · live transition feed (deos-js card)",
            ModeCard::Agent => "agent · live mandate + activity (deos-js card)",
            ModeCard::Links => "what-links-here · live backlinks (deos-js card)",
            ModeCard::Proofs => "proofs · live verification status (deos-js card)",
            ModeCard::Organs => "organs · live organ cell-state (deos-js card)",
            ModeCard::Home => "home · the live landing portal (deos-js card)",
            ModeCard::Inspector => "inspect · live cell state + affordances (deos-js card)",
        }
    }

    /// GENERATE this card's view-tree from the live ledger (the card's OWN public
    /// view-builder), focused on `focus` where the card is per-cell (links / agent).
    fn view_tree(self, world: &World, focus: CellId, viewer: &AuthRequired) -> ViewTree {
        let ledger = world.ledger();
        match self {
            ModeCard::Composer => {
                // The composer authors a document cell; over the cockpit's image we open
                // it on a host derived from the focused cell and read its (initially empty)
                // composition's view-tree — the surface a real authoring gesture grows.
                let host = deos_js::composer_card::ChildCellId(u128::from_le_bytes(
                    focus.as_bytes()[..16].try_into().unwrap_or([0u8; 16]),
                ));
                let card = deos_js::composer_card::ComposerCard::open(
                    host,
                    Author(0xC0),
                    viewer.clone(),
                    AuthRequired::Signature,
                );
                deos_js::composer_card::composer_view(&card)
            }
            ModeCard::Objects => deos_js::objects_card::objects_view(ledger),
            ModeCard::Graph => deos_js::graph_card::graph_view(ledger),
            ModeCard::Dynamics => {
                // The feed view over the live image's transitions — read off the cockpit's
                // own dynamics log (every committed turn lands here), most-recent kept.
                let entries: Vec<deos_js::FeedEntry> = world
                    .dynamics()
                    .all()
                    .iter()
                    .filter_map(|ev| match ev {
                        crate::dynamics::WorldEvent::TurnCommitted { height, agent, .. } => Some(
                            deos_js::FeedEntry::new(*height, ev.label(), agent.as_bytes()),
                        ),
                        _ => None,
                    })
                    .collect();
                deos_js::dynamics_card::feed_view(&entries)
            }
            ModeCard::Agent => {
                // The agent card: the focused cell's mandate (its c-list edges, off the
                // live ledger) + its recent cap-gated turns (the dynamics rows it authored).
                let mandate = deos_js::agent_card::read_mandate(ledger, focus);
                let actions: Vec<deos_js::AgentAction> = world
                    .dynamics()
                    .all()
                    .iter()
                    .filter_map(|ev| match ev {
                        crate::dynamics::WorldEvent::TurnCommitted {
                            height,
                            agent,
                            receipt_hash,
                            ..
                        } if *agent == focus => {
                            Some(deos_js::AgentAction::new(*height, ev.label(), receipt_hash))
                        }
                        _ => None,
                    })
                    .collect();
                deos_js::agent_card::agent_view(&mandate, &actions)
            }
            ModeCard::Links => {
                // What-links-here over the focused cell, across the live image's cells (the
                // backlink web the viewer is cleared to see — fail-closed per is_attenuation).
                let cells: Vec<CellId> = ledger.iter().map(|(id, _)| *id).collect();
                let (backlinks, total) =
                    deos_js::links_card::build_backlinks(focus, &cells, viewer);
                deos_js::links_card::links_view(focus, viewer, &backlinks, total)
            }
            ModeCard::Proofs => {
                // The proof board over the live image (most-recent-first, capped) → one card
                // row per committed turn, tier-tagged for the renderer's styling accent.
                let board = crate::proofs::ProofBoard::build(world, 16);
                let rows: Vec<deos_js::ProofCardRow> = board
                    .entries
                    .iter()
                    .map(|e| deos_js::ProofCardRow {
                        height: e.height,
                        receipt_short: e.receipt_short.clone(),
                        tier_label: e.tier.label().to_string(),
                        tag: proof_tier_tag(e.tier),
                        summary: e.summary(),
                        route: e.upgrade_route().map(|s| s.to_string()),
                    })
                    .collect();
                deos_js::proofs_view(
                    board.by_construction,
                    board.signed,
                    board.stark_attached,
                    &rows,
                )
            }
            ModeCard::Organs => {
                // The organ survey over the live image → three groups (trustlines · flash
                // wells · remote-path), each a section of organ rows.
                let survey = crate::organs::OrganSurvey::build(world);
                let trustlines: Vec<deos_js::OrganCardRow> = survey
                    .trustlines
                    .iter()
                    .map(|t| deos_js::OrganCardRow {
                        glyph: "⬡".to_string(),
                        short: format!("{} (trustline)", t.short),
                        summary: t.summary(),
                    })
                    .collect();
                let flash_wells: Vec<deos_js::OrganCardRow> = survey
                    .flash_wells
                    .iter()
                    .map(|f| deos_js::OrganCardRow {
                        glyph: "⬡".to_string(),
                        short: format!("{} (flash well)", f.short),
                        summary: f.summary(),
                    })
                    .collect();
                let remote: Vec<deos_js::OrganCardRow> = survey
                    .remote
                    .iter()
                    .map(|r| deos_js::OrganCardRow {
                        glyph: "◌".to_string(),
                        short: format!("{} (remote)", r.kind),
                        summary: format!("seam {} · route {}", r.seam, r.route),
                    })
                    .collect();
                deos_js::organs_view(
                    survey.live_count(),
                    survey.remote.len(),
                    &trustlines,
                    &flash_wells,
                    &remote,
                )
            }
            ModeCard::Home => {
                // The landing portal over the live image (its numbers are the running image's
                // actual numbers) → the masthead (liveness pills) + a section per portal section.
                let portal = crate::landing::LandingPortal::build(world);
                let pills: Vec<(String, String)> = vec![
                    ("● live".to_string(), "good".to_string()),
                    ("embedded verified executor".to_string(), "good".to_string()),
                    (format!("h{}", world.height()), "accent".to_string()),
                    (
                        format!("{} cells", world.cell_count()),
                        "accent".to_string(),
                    ),
                    (
                        format!("{} receipts", world.receipts().len()),
                        "accent".to_string(),
                    ),
                ];
                let sections: Vec<deos_js::HomeSection> = portal
                    .sections
                    .iter()
                    .map(|s| deos_js::HomeSection {
                        title: s.title.clone(),
                        lines: s
                            .lines
                            .iter()
                            .map(|l| deos_js::HomeLine {
                                text: l.text.clone(),
                                heading: matches!(l.tone, crate::landing::Tone::Heading),
                            })
                            .collect(),
                    })
                    .collect();
                deos_js::home_view(
                    &portal.headline,
                    &portal.subtitle,
                    &pills,
                    &sections,
                    &portal.invitation,
                )
            }
            ModeCard::Inspector => {
                // The inspector view-tree over the focused cell: its RawFields face (scalar
                // state slots → live `Bind` rows, structural substances → labeled `Text`)
                // and its cap-gated affordances (a `Button` per affordance the holder of
                // `viewer` may fire). The affordance spec MATCHES the one
                // `build_mode_card_surface` registers on the attached applet (`bump`,
                // Signature), so the surfaced button fires a REAL cap-gated verified turn on
                // the live ledger. `escalate` (Proof) is offered to the surface too so the
                // cap tooth is genuinely exercised: `project_for(viewer)` never surfaces it
                // as a button for a Signature holder (the over-reach is refused in-band).
                let specs = vec![
                    ("bump".to_string(), AuthRequired::Signature),
                    ("escalate".to_string(), AuthRequired::Proof),
                ];
                deos_js::inspector_card::inspector_view_for(focus, ledger, &specs, viewer)
            }
        }
    }
}

/// **Mount a landed card as a cockpit mode's main-pane surface** — the generalization of
/// [`build_inspector_card_surface`] to the other six cards. The view-tree is GENERATED in
/// Rust from the live ledger ([`ModeCard::view_tree`]), bridged to the renderer's
/// [`ViewNode`] through the canonical JSON shape, and hosted as a [`CardPane`] over an
/// applet ATTACHED to the cockpit's live `World` (so a `bind` re-reads the operator's real
/// cell and an affordance button fires ONE cap-gated verified turn on that World).
///
/// The mount also adopts the view as an editable `ViewTree` document (a [`CardEditor`] over
/// a portable applet seeded with the view-source) so [`ModeCardSurface::edit_view`] can
/// reshape the surface live (the edit-from-within route — re-fold then rebuild the pane).
///
/// `held` is the operator's authority the affordance fires + the view-edits mount under. A
/// build error is returned for the caller to surface fail-soft (the Rust panel stays).
#[allow(clippy::result_large_err)]
pub fn build_mode_card_surface(
    id: u64,
    kind: ModeCard,
    world: Rc<RefCell<World>>,
    focus: CellId,
    held: AuthRequired,
    cx: &mut App,
) -> Result<ModeCardSurface, String> {
    // The card's affordance surface over the focused cell: `bump` (Signature — held,
    // admitted) advances a state slot so a fired button visibly moves a bound row. The
    // fire commits THROUGH `World::commit_turn` onto the live ledger.
    let affordances = vec![("bump".to_string(), AuthRequired::Signature)];

    // GENERATE the card's view-tree from the live ledger BEFORE attaching (the builder
    // reads the World through a shared borrow; the attach takes the `Rc` next).
    let tree_doc: ViewTree = {
        let w = world.borrow();
        kind.view_tree(&w, focus, &held)
    };

    // Attach an applet to the LIVE cockpit World, focused on `focus` — the card's
    // substance is the operator's REAL cell; a fire lands on the ledger the inspector reads.
    let sink = WorldSinkAdapter::live(world);
    let attached = attach_agent(sink, focus, held.clone(), affordances);

    // Bridge the view-tree into the renderer's `ViewNode` through the canonical JSON shape.
    let view_json = tree_doc.to_json();
    let tree: ViewNode = deos_view::parse_view_tree(&view_json)
        .map_err(|e| format!("{:?} view-tree bridge: {e}", kind))?;

    // Adopt the view as an editable document (the edit-from-within route): a `CardEditor`
    // over a portable applet seeded with the view-source. `held == edit_authority` so the
    // reshape is authorized (the operator may reshape their own surface); an unauthorized
    // hand would be refused in-band by the same `is_attenuation` cap tooth.
    let manifest = AppletManifest {
        seed_fields: vec![(AGENT_COUNTER_SLOT, 0u64)],
        affordances: Vec::new(),
        held: held.clone(),
        view_source: view_json,
    };
    let card_pk = mode_card_pk(kind, focus);
    let portable = PortableApplet::mint(card_pk, [0u8; 32], &manifest);
    let editor = CardEditor::adopt(
        portable,
        manifest,
        Author(0xED),
        held.clone(),
        AuthRequired::Signature,
    );

    // Share the live attached applet so the rendered buttons + the binds both drive the
    // SAME sovereign cell on the live ledger.
    let shared: SharedAttached = Rc::new(RefCell::new(attached));

    let pane_applet = shared.clone();
    let pane_tree = tree.clone();
    let title = kind.title();
    let entity = cx.new(|_cx| CardPane::new(pane_applet, pane_tree, title));

    Ok(ModeCardSurface {
        id: SurfaceId(id),
        kind,
        entity,
        applet: shared,
        editor: Rc::new(RefCell::new(editor)),
        focus,
    })
}

/// A deterministic provenance pk for a mode card's editable view document, keyed on the
/// card kind + the focused cell (so two mounts of the same kind over different focuses get
/// distinct provenance chains, and a rebuild over the same focus is stable).
fn mode_card_pk(kind: ModeCard, focus: CellId) -> [u8; 32] {
    let mut pk = [0u8; 32];
    pk[..32].copy_from_slice(focus.as_bytes());
    pk[0] ^= match kind {
        ModeCard::Composer => 0xC0,
        ModeCard::Objects => 0x0B,
        ModeCard::Graph => 0x6A,
        ModeCard::Dynamics => 0xD7,
        ModeCard::Agent => 0xA9,
        ModeCard::Links => 0x11,
        ModeCard::Proofs => 0x9F,
        ModeCard::Organs => 0x06,
        ModeCard::Home => 0x40,
        ModeCard::Inspector => 0x15,
    };
    pk
}

/// The renderer's styling-accent tag for a verification tier (the existing `props.tag`
/// convention the pill/section nodes read): STARK is the strongest (`good`), an
/// executor-signed turn `accent`, a verified-by-construction turn `muted`.
fn proof_tier_tag(tier: crate::proofs::VerificationTier) -> String {
    match tier {
        crate::proofs::VerificationTier::StarkAttached => "good",
        crate::proofs::VerificationTier::ExecutorSigned => "accent",
        crate::proofs::VerificationTier::VerifiedByConstruction => "muted",
    }
    .to_string()
}

/// **MAKE YOUR FIRST CARD** — mint a fresh, editable starter card over the cockpit's LIVE
/// `World`, the substance being the stranger's OWN `home` cell. This is the onboarding
/// keystone: the path from "I'm in" to "I made a thing." A first-timer clicks one
/// affordance and THIS builds them a real card that is theirs —
///
///   - a friendly title, a LIVE bound count (re-reads their home cell's counter slot off
///     the ledger), and a `+1` button that fires ONE cap-gated verified turn on a cell they
///     own (a real receipt on their own tape), and
///   - an editable view document (a [`CardEditor`] under their `held` authority), so the
///     two onboarding edit affordances ("add a button", "rename the title") each apply a
///     **receipted patch with blame** through [`ModeCardSurface::edit_view`] — the card
///     re-folds + repaints live, and the change is an accountable patch, not a recompile.
///
/// The returned [`ModeCardSurface`] is the SAME type the mode cards mount, so the card
/// inherits `edit_view` / `view_source` / the `CardPane` host for free — the onboarding
/// card is a first-class live card, not a special case. Its `kind` is borrowed
/// ([`ModeCard::Objects`]) only to satisfy the surface struct; nothing reads it for the
/// first card (the view-tree is hand-authored here, never regenerated from the ledger).
///
/// `home` is the stranger's own cell (their `user` anchor — "your home") and `held` is the
/// authority their affordance fires + view-edits mount under (`Signature`, the attenuated
/// operator hand; it satisfies the card's edit_authority, so the reshape is authorized).
#[allow(clippy::result_large_err)]
pub fn build_first_card_surface(
    id: u64,
    world: Rc<RefCell<World>>,
    home: CellId,
    held: AuthRequired,
    cx: &mut App,
) -> Result<ModeCardSurface, String> {
    // The card's affordance surface over the stranger's home cell: `bump` (Signature —
    // held, admitted) advances the home cell's counter slot so the `+1` visibly moves the
    // bound row. The fire commits THROUGH `World::commit_turn` onto the live ledger.
    let affordances = vec![("bump".to_string(), AuthRequired::Signature)];

    // THE STARTER VIEW — hand-authored (NOT regenerated from the ledger): a welcoming
    // title, a live `bind` on the home cell's counter slot, and a `+1` button firing `bump`.
    // This is the card a first-timer is handed; the onboarding edit affordances then grow it.
    let tree_doc = ViewTree::VStack {
        children: vec![
            ViewTree::Text {
                props: deos_js::card_editor::TextProps {
                    text: "my first card".into(),
                },
            },
            ViewTree::Text {
                props: deos_js::card_editor::TextProps {
                    text: "this card is yours — its +1 fires a real verified turn.".into(),
                },
            },
            ViewTree::Bind {
                props: deos_js::card_editor::BindProps {
                    slot: AGENT_COUNTER_SLOT,
                    label: "count: ".into(),
                },
            },
            ViewTree::Button {
                props: deos_js::card_editor::ButtonProps {
                    label: "+1".into(),
                    on_click: deos_js::card_editor::OnClick {
                        turn: "bump".into(),
                        arg: 1,
                    },
                },
            },
        ],
    };

    // Attach an applet to the LIVE cockpit World, focused on `home` — the card's substance
    // is the stranger's REAL cell; a `+1` lands on the ledger their inspector reads.
    let sink = WorldSinkAdapter::live(world);
    let attached = attach_agent(sink, home, held.clone(), affordances);

    // Bridge the starter view-tree into the renderer's `ViewNode` through the canonical JSON.
    let view_json = tree_doc.to_json();
    let tree: ViewNode = deos_view::parse_view_tree(&view_json)
        .map_err(|e| format!("first-card view-tree bridge: {e}"))?;

    // Adopt the view as an editable document — the onboarding edit-from-within route. A
    // distinct provenance pk (the home cell, tagged) so the first card's authoring chain is
    // its own. `held == edit_authority` so the stranger may reshape their own card; an
    // unauthorized hand would be refused in-band by the same `is_attenuation` cap tooth.
    let manifest = AppletManifest {
        seed_fields: vec![(AGENT_COUNTER_SLOT, 0u64)],
        affordances: Vec::new(),
        held: held.clone(),
        view_source: view_json,
    };
    let mut card_pk = [0u8; 32];
    card_pk.copy_from_slice(home.as_bytes());
    card_pk[0] ^= 0xF1; // the "first card" provenance tag (distinct from the mode-card pks)
    let portable = PortableApplet::mint(card_pk, [0u8; 32], &manifest);
    let editor = CardEditor::adopt(
        portable,
        manifest,
        Author(0xF1),
        held.clone(),
        AuthRequired::Signature,
    );

    // Share the live attached applet so the rendered button + the bind both drive the SAME
    // sovereign cell on the live ledger.
    let shared: SharedAttached = Rc::new(RefCell::new(attached));

    let pane_applet = shared.clone();
    let pane_tree = tree.clone();
    let entity = cx.new(|_cx| CardPane::new(pane_applet, pane_tree, "my first card"));

    Ok(ModeCardSurface {
        id: SurfaceId(id),
        // The first card borrows a kind to satisfy the struct; nothing regenerates its view
        // from the ledger (the view-tree is hand-authored above + grown by the edit route).
        kind: ModeCard::Objects,
        entity,
        applet: shared,
        editor: Rc::new(RefCell::new(editor)),
        focus: home,
    })
}

/// A landed card mounted as a cockpit mode's main-pane surface — the [`CardPane`] gpui
/// entity (rendered over the live World), the shared live applet (so a fire lands on the
/// operator's real cell), and the editable view document (a [`CardEditor`], the
/// edit-from-within route). Held by the cockpit per mounted mode; the entity is hosted as
/// the mode's surface body.
pub struct ModeCardSurface {
    id: SurfaceId,
    kind: ModeCard,
    entity: Entity<CardPane>,
    applet: SharedAttached,
    /// The editable view document — a `CardEditor` over a portable applet seeded with the
    /// view-source. A `ViewPatch` re-folds it; the re-folded tree rebuilds the `CardPane`.
    editor: Rc<RefCell<CardEditor>>,
    focus: CellId,
}

impl ModeCardSurface {
    /// Which card this surface mounts.
    pub fn kind(&self) -> ModeCard {
        self.kind
    }

    /// The focused cell the view-tree was generated over (so the host rebuilds when the
    /// focus moves — the same discipline as the inspector card).
    pub fn focus(&self) -> CellId {
        self.focus
    }

    /// The shared live applet handle (so the host/test can read the live ledger / receipt
    /// count after a button fire — the SAME applet the card drives).
    pub fn applet(&self) -> SharedAttached {
        self.applet.clone()
    }

    /// The on-ledger receipt count on the card's live tape (genuine committed turns).
    pub fn receipt_count(&self) -> usize {
        self.applet.borrow().receipt_count()
    }

    /// The [`CardPane`] gpui entity (so the cockpit hosts the card's body directly as the
    /// mode's main-pane surface — the card-as-surface mount).
    pub fn entity_handle(&self) -> Entity<CardPane> {
        self.entity.clone()
    }

    /// **EDIT THE SURFACE FROM WITHIN — the open seam, now wired.** Route a `ViewPatch`
    /// (deos.editor/edit_view) through the editable view document: the [`CardEditor`]
    /// applies the structural gesture as a *receipted patch with blame* (refused in-band
    /// if `held` does not satisfy the card's `edit_authority`), then the re-folded
    /// `ViewTree` is bridged to a `ViewNode` and swapped into the live [`CardPane`] — so
    /// the surface repaints reshaped on the next frame. The live applet (the substance
    /// binds/fires drive) is untouched; only the view changed. A live `&mut Context` is
    /// needed to update the entity, so this runs on a cockpit handler.
    pub fn edit_view<T: 'static>(
        &self,
        patch: ViewPatch,
        cx: &mut Context<T>,
    ) -> Result<(), String> {
        let edit = self
            .editor
            .borrow_mut()
            .edit_view(patch)
            .map_err(|e| format!("edit-from-within refused: {e}"))?;
        // Re-bridge the re-folded view-tree into the renderer's `ViewNode` and swap it in.
        let view_json = edit.tree.to_json();
        let tree: ViewNode = deos_view::parse_view_tree(&view_json)
            .map_err(|e| format!("reshaped view-tree bridge: {e}"))?;
        self.entity.update(cx, |card, cx| {
            card.set_tree(tree);
            cx.notify();
        });
        Ok(())
    }

    /// The current view-source JSON of the editable document (so a host/test can assert the
    /// reshape landed in the document, not just the rendered tree).
    pub fn view_source(&self) -> String {
        self.editor.borrow().view_source()
    }
}

impl CockpitSurface for ModeCardSurface {
    fn item_id(&self) -> SurfaceId {
        self.id
    }

    fn tab_label(&self) -> SharedString {
        SharedString::from("card")
    }

    fn render_body(&mut self, _window: &mut Window, cx: &mut App) -> AnyElement {
        // Immediate-mode binds re-read the live ledger at render time, so a notify each
        // frame keeps a bound row current after a fire (mirrors `CardSurface`).
        self.entity.update(cx, |_card, cx| cx.notify());
        div()
            .size_full()
            .child(self.entity.clone())
            .into_any_element()
    }

    fn focus_handle(&self, cx: &App) -> FocusHandle {
        cx.focus_handle()
    }

    fn boxed_clone(&self) -> Box<dyn CockpitSurface> {
        Box::new(ModeCardSurface {
            id: self.id,
            kind: self.kind,
            entity: self.entity.clone(),
            applet: self.applet.clone(),
            editor: self.editor.clone(),
            focus: self.focus,
        })
    }
}

// ===========================================================================
// FULL VIEW MOUNTING — a launched starbridge-app's BESPOKE card as a dock pane.
//
// Where `build_*card_surface` mount the cockpit's own reflective cards (counter /
// inspector / mode cards) over a deos-js `AttachedApplet`, THIS mounts a launched
// app's OWN `deos.ui.*` card (`starbridge-apps/<app>/src/card.rs`) over the
// app-framework substance (`crate::app_registry::AppCardSubstance`) — so launching
// gallery shows GALLERY's card UI, and clicking its "Submit" button fires gallery's
// REAL cap-gated verified turn through the app's spine onto the cockpit's live World
// (the SAME ledger the inspector reads). Same `CardPane` renderer, same dock-mount,
// a different substance.
// ===========================================================================

/// A launched starbridge-app's bespoke card mounted as a [`CockpitSurface`] — the
/// [`CardPane`] gpui entity (over the live World) + the shared [`AppCardSubstance`]
/// (the app's spine the rendered buttons fire through + the binds re-read).
#[cfg(feature = "app-registry")]
pub struct AppCardSurface {
    id: SurfaceId,
    /// The launched app's display name (the dock tab label).
    name: SharedString,
    entity: Entity<CardPane>,
    /// The shared app-card substance (kept so a host can read live state / fire count;
    /// the SAME backing the rendered widgets drive).
    substance: Rc<RefCell<crate::app_registry::AppCardSubstance>>,
    focus: FocusHandle,
}

#[cfg(feature = "app-registry")]
impl AppCardSurface {
    /// The launched app's primary cell on the live World (the inspector's pointer).
    pub fn app_cell(&self) -> CellId {
        self.substance.borrow().app_cell()
    }

    /// The [`CardPane`] gpui entity (so a host can mount the card body directly).
    pub fn entity_handle(&self) -> Entity<CardPane> {
        self.entity.clone()
    }
}

/// **Mount a LAUNCHED app's bespoke card as a dock surface.** Takes the
/// [`crate::app_registry::LaunchedOnWorld`] the launcher already produced (so the app is
/// launched ONCE — its cell + first receipt are already on the live World), resolves the
/// app's wired card ([`crate::app_registry::app_card`]), parses its `deos.ui.*` JSON into
/// a [`ViewNode`] ([`deos_view::parse_view_tree`]), and hosts it as a [`CardPane`] over an
/// [`crate::app_registry::AppCardSubstance`] built on the launch's spine. The card's
/// buttons then fire the app's REAL verified turns; its `bind`s re-read the app cell off
/// the live World ledger.
///
/// `None` (an `Err`) if the app ships no wired card, or its JSON fails to parse — the
/// caller keeps the launch's inspect behavior as the fallback (the card is additive).
#[cfg(feature = "app-registry")]
#[allow(clippy::result_large_err)]
pub fn build_app_card_surface(
    id: u64,
    app_id: &str,
    app_name: &str,
    launched: crate::app_registry::LaunchedOnWorld,
    cx: &mut App,
) -> Result<AppCardSurface, String> {
    let card = crate::app_registry::app_card(app_id)
        .ok_or_else(|| format!("app '{app_id}' ships no wired card"))?;

    // Parse the app's renderer-independent `deos.ui.*` card into the renderer's `ViewNode`.
    let tree: ViewNode = deos_view::parse_view_tree(&card.json)
        .map_err(|e| format!("'{app_id}' card view-tree parse: {e}"))?;

    // Build the live substance over the launch's spine + the card's fire dispatch (the
    // app is NOT relaunched — `launched.spine` is the cell already on the live World).
    let substance = Rc::new(RefCell::new(crate::app_registry::AppCardSubstance::new(
        launched.spine,
        card.fire,
    )));

    let sub_dyn: CardSubstanceRef = substance.clone();
    let title = format!("{app_name} · live app card (deos-view)");
    let entity = cx.new(|_cx| CardPane::new_substance(sub_dyn, tree, title));

    Ok(AppCardSurface {
        id: SurfaceId(id),
        name: SharedString::from(app_name.to_string()),
        entity,
        substance,
        focus: cx.focus_handle(),
    })
}

#[cfg(feature = "app-registry")]
impl CockpitSurface for AppCardSurface {
    fn item_id(&self) -> SurfaceId {
        self.id
    }

    fn tab_label(&self) -> SharedString {
        self.name.clone()
    }

    fn render_body(&mut self, _window: &mut Window, cx: &mut App) -> AnyElement {
        // Immediate-mode binds re-read the live World at render time, so notify each
        // frame keeps a bound row current after a fire (mirrors `CardSurface`).
        self.entity.update(cx, |_card, cx| cx.notify());
        div()
            .size_full()
            .child(self.entity.clone())
            .into_any_element()
    }

    fn focus_handle(&self, _cx: &App) -> FocusHandle {
        self.focus.clone()
    }

    fn boxed_clone(&self) -> Box<dyn CockpitSurface> {
        Box::new(AppCardSurface {
            id: self.id,
            name: self.name.clone(),
            entity: self.entity.clone(),
            substance: self.substance.clone(),
            focus: self.focus.clone(),
        })
    }
}
