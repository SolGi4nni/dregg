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
    div, AnyElement, App, AppContext, Entity, FocusHandle, IntoElement, ParentElement,
    SharedString, Styled, Window,
};

use deos_view::ViewNode;
use dregg_cell::{AuthRequired, CellId};

use crate::agent_attach::{attach_agent, WorldSinkAdapter, AGENT_COUNTER_SLOT};
use crate::card_pane::{build_card_over_live, CardPane, SharedAttached};
use crate::world::World;

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
    let entity = cx.new(|_cx| {
        CardPane::new(
            pane_applet,
            pane_tree,
            "hyperdreggmedia · counter card",
        )
    });

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
