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

use deos_js::card_editor::{
    ButtonProps, CardEditor, GridProps, IconProps, OnClick, PillProps, SectionProps, TextProps,
    ViewPatch,
};
use deos_js::portable::{AppletManifest, PortableApplet};
use deos_js::{Author, ViewTree};

use crate::reflect::FieldValue;
use crate::service_directory::{ServiceDirectory, ServiceFilter, ServiceKind};
use crate::trust_panel::TrustPanel;
use crate::web_cells::WebCellsBrowser;
use crate::wonder::WonderRoom;

use crate::agent_attach::{attach_agent, WorldSinkAdapter, AGENT_COUNTER_SLOT};
use crate::card_pane::{
    build_card_over_live, CardPane, CardSubstance, CardSubstanceRef, SharedAttached,
};
use crate::world::World;

use deos_matrix::chat_card::ChatCard;
use deos_matrix::chat_view::{chat_view_json, CHAT_DRAFT_KEY, CHAT_SEND_TURN, CHAT_TURNS_SLOT};

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

// ===========================================================================
// SURFACE-STATE THREADING — the cockpit-side state a STATEFUL card needs that
// the live `World` alone does not carry.
//
// The reflective survey cards (objects / graph / proofs / …) are pure functions
// of the live ledger, so `view_tree(world, focus, viewer)` is enough. But the
// STATEFUL surfaces (Cipherclerk / Debugger / Replay) render cockpit-OWNED state
// that is NOT on the ledger: the live HD-identity clerk, the turn under the
// debugger's lens + its breakpoints, the replay scrubber cursor + pinned fork.
// Carding those over the bare-`world` mount would show STALE data (an empty
// clerk, a genesis cursor) — a regression in honesty. `SurfaceState` threads the
// live cockpit state INTO the mount so a carded surface renders the SAME live
// state its gpui panel shows.
//
// Every field is OPTIONAL: a stateless card ignores it (`SurfaceState::default()`
// is empty), so the existing cards build byte-identically.
// ===========================================================================

/// The live cockpit-side state a stateful [`ModeCard`] reads (additive; a
/// stateless card ignores it). Borrowed for the duration of one card build.
#[derive(Clone, Copy, Default)]
pub struct SurfaceState<'a> {
    /// CIPHERCLERK · the live HD-derived identity vault.
    pub clerk: Option<&'a crate::cipherclerk::Cipherclerk>,
    /// DEBUGGER · the turn under inspection + its active breakpoints.
    pub debugger: Option<DebuggerState<'a>>,
    /// REPLAY · the scrubber cursor + an optional pinned what-if fork (the
    /// recorded history itself is read off the live `World`).
    pub replay: Option<ReplayState<'a>>,
    /// SWARM · the live A2 swarm coordinator (+ the optional killer-demo script).
    pub swarm: Option<SwarmCardState<'a>>,
}

/// The SWARM surface's cockpit-side state: the live [`crate::swarm::Swarm`] coordinator (the
/// members · inboxes · activity · budget are read off it, NOT the ledger) and the optional
/// killer-demo (N5 pug-handoff) script the Swarm tab drives. Borrowed for one card build.
#[derive(Clone, Copy)]
pub struct SwarmCardState<'a> {
    /// The live swarm coordinator the card surveys ([`crate::swarm::SwarmView::build`]).
    pub swarm: &'a crate::swarm::Swarm,
    /// The killer-demo script (frame cursor · next step · the Stingray budget), if booted.
    pub demo: Option<&'a crate::demo::HeadlineDemo>,
    /// The captured killer-demo frame transcript (the run lines), as the panel shows them.
    pub demo_lines: &'a [String],
}

/// The DEBUGGER surface's cockpit-side state: the turn under the lens + the
/// breakpoints the operator armed. (The world is the card mount's own `world`,
/// against which [`crate::debug::render`] re-executes the turn faithfully.)
#[derive(Clone, Copy)]
pub struct DebuggerState<'a> {
    /// The turn the debugger inspects (re-executed against the live World).
    pub turn: &'a dregg_turn::turn::Turn,
    /// The breakpoints evaluated over the turn's steps.
    pub breakpoints: &'a [crate::debug::Breakpoint],
}

/// The REPLAY surface's cockpit-side state: the scrubber cursor + an optional
/// pinned fork. The recorded history is read off the live `World`
/// ([`crate::world::World::recorded_turns`]), so it is not threaded here.
#[derive(Clone, Copy)]
pub struct ReplayState<'a> {
    /// The scrubber cursor (a step in `0..=history.len()`).
    pub cursor: usize,
    /// An optional pinned what-if fork to summarize.
    pub fork: Option<&'a crate::replay::Fork>,
}

/// Which landed card a [`ModeCardSurface`] mounts — the deos-js card that IS a given
/// cockpit mode's main-pane surface. Each names a `deos_js::*_card` whose view-tree is a
/// pure function of the live ledger (plus a focus, for the links card; plus a
/// [`SurfaceState`] for the stateful cards).
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
    /// SERVICES · the whole-image service directory (`crate::service_directory`). A survey
    /// of every service-publishing cell in the live image (each interface derived live),
    /// rendered as a summary pill row + one row per service (handle · kind · interface ·
    /// method count · an ANNOUNCED badge). Read-only: the genuine ANNOUNCE (a real verified
    /// turn) lives in the gpui directory panel, which stays as the card-pane-off fallback +
    /// the deployed default (the same card-as-alternative posture as the other mode cards).
    ServiceDirectory,
    /// AUTHOR/BROWSE · the `dregg://` web-of-cells (`crate::web_cells`). A survey of the
    /// addressable cells (each a real attested fetch), rendered as one row per page
    /// (`dregg://` uri · preview · an attested/unverified badge). Read-only.
    WebCells,
    /// TRUST · the human-layer who-i-am + recovery surface (`crate::trust_panel`). The
    /// identity card (devices + guardians as labeled rows), the recovery gauge, and the
    /// key-event-log (KEL) timeline — all real projections off the identity decode.
    /// Read-only.
    Trust,
    /// WONDER · the glowing-cell room (`crate::wonder`) — the 1999-AOL front door, reborn as a
    /// portable card. Every ledger cell becomes a tile in a spatial `grid`, its glow `icon`
    /// (✦ alive / ○ quiet) a live projection of the recent dynamics stream, each carrying a
    /// `look` button. A pure function of the live World (`WonderRoom::build`); read-mostly (the
    /// drag-value grab/drop conserving turn stays in the gpui room). The card the new
    /// `grid`/`icon` vocabulary was built for.
    Wonder,
    /// DEV · the cipherclerk vault (`crate::cipherclerk`) — the agent's HD-derived signing
    /// identities, the capability tokens they hold, and the recipient-targeted delegations,
    /// each a uniform reflective object. COCKPIT-STATEFUL: reads the live `Cipherclerk`
    /// threaded through [`SurfaceState::clerk`] (NOT the ledger), so a mint/attenuate/delegate
    /// the operator just fired shows live. Read-only card (the genuine crypto stays in the
    /// gpui panel, the card-pane-off fallback).
    Cipherclerk,
    /// DEV · the step-debugger (`crate::debug`) — the turn under the lens re-executed faithfully
    /// against the live World, its per-effect step list with conservation deltas, the refusal
    /// explanation (the prize) or the conserving-commit line, and the witness inspection.
    /// COCKPIT-STATEFUL: the turn + breakpoints come through [`SurfaceState::debugger`].
    /// Read-only card.
    Debugger,
    /// DEV · the replay / time-travel scrubber (`crate::replay`) — the recorded history timeline,
    /// the VERIFIED reconstruction at the cursor (root-checked), the prev-step diff, and a pinned
    /// what-if fork's divergence. COCKPIT-STATEFUL: the cursor + fork come through
    /// [`SurfaceState::replay`] (the history is read off the live World). Read-only card.
    Replay,
    /// OPERATE · the A2 swarm coordinator (`crate::swarm`) — N agent cells coordinating as
    /// cap-confined Surface cells: each member's mandate/backing/balance + its notify-edge inbox,
    /// the aggregate budget strip, the killer-demo (N5 pug-handoff) frame/budget headline, and the
    /// activity feed of executor receipts + notify edges. COCKPIT-STATEFUL: the live `Swarm` (and
    /// the optional killer-demo) come through [`SurfaceState::swarm`] (the coordinator is cockpit
    /// state, NOT the ledger). Read-only card (the genuine emit/drain/transfer turns stay in the
    /// gpui panel, the card-pane-off fallback).
    Swarm,
    /// SERVICES · the per-cell service explorer (`crate::service_explorer`) — the focused cell's
    /// DERIVED interface as the viewer sees it: one row per declared method (name · arity · auth ·
    /// replayable/serviced semantics · the cap badge `authorized`). A pure function of the live
    /// World + focus (`ServiceExplorer::build`); read-only (the genuine method invocation — a real
    /// verified turn — stays in the gpui panel).
    ServiceExplorer,
    /// SERVICES · the powerbox / CapDesk designation surface (`crate::powerbox`) — the focused cell
    /// as the granter, a standing app request, and the picker of GRANTABLE targets (every cell the
    /// granter actually holds a cap reaching, read live off its c-list — `mint_needs_held_factory`
    /// made visible). A pure function of the live World + focus (`Powerbox::present`); read-only (the
    /// genuine designation — a real attenuated grant turn — stays in the gpui panel).
    Powerbox,
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
            ModeCard::ServiceDirectory => "directory · live services (deos-js card)",
            ModeCard::WebCells => "web-of-cells · live dregg:// docuverse (deos-js card)",
            ModeCard::Trust => "trust · who-i-am + recovery (deos-js card)",
            ModeCard::Wonder => "wonder · the glowing room (deos-js card)",
            ModeCard::Cipherclerk => {
                "cipherclerk · identities · tokens · delegations (deos-js card)"
            }
            ModeCard::Debugger => "debugger · step · inspect · explain (deos-js card)",
            ModeCard::Replay => "replay · verified time-travel (deos-js card)",
            ModeCard::Swarm => "swarm · multi-agent cap-coordination (deos-js card)",
            ModeCard::ServiceExplorer => "explorer · live service interface (deos-js card)",
            ModeCard::Powerbox => "powerbox · CapDesk designation (deos-js card)",
        }
    }

    /// GENERATE this card's view-tree from the live ledger (the card's OWN public
    /// view-builder), focused on `focus` where the card is per-cell (links / agent), and
    /// reading the cockpit-side `state` where the card is stateful (cipherclerk / debugger /
    /// replay). The stateless cards ignore `state`.
    fn view_tree(
        self,
        world: &World,
        focus: CellId,
        viewer: &AuthRequired,
        state: &SurfaceState,
    ) -> ViewTree {
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
            ModeCard::ServiceDirectory => {
                // The whole-image directory survey: discover every service-publishing cell
                // off the live ledger (each interface derived live), rendered as data.
                let dir = ServiceDirectory::discover(world, &ServiceFilter::default());
                service_directory_view(&dir)
            }
            ModeCard::WebCells => {
                // The dregg:// web-of-cells over the live image, projected for the focused
                // cell as the viewer (the same membrane the gpui panel projects through).
                let browser = WebCellsBrowser::build(world, focus, viewer.clone(), None);
                web_cells_view(&browser)
            }
            // The trust surface is a projection off the identity decode (a representative
            // identity until an on-ledger identity cell is wired — the same posture as the
            // gpui `trust_tab`), so it does not read the cockpit's `world`.
            ModeCard::Trust => trust_view(&TrustPanel::demo()),
            ModeCard::Wonder => {
                // The glowing room over the live image — every cell a tile, its glow a live
                // projection of the recent dynamics stream (a pure function of `world`).
                let room = WonderRoom::build(world);
                wonder_view(&room)
            }
            ModeCard::Cipherclerk => {
                // The clerk vault is cockpit-side state (NOT on the ledger), threaded through
                // `state.clerk`. Absent (a stateless/default build) → an honest empty state
                // rather than a fabricated roster.
                match state.clerk {
                    Some(clerk) => cipherclerk_view(&crate::cipherclerk::render(clerk)),
                    None => empty_state_view(
                        "⚷ The cipherclerk",
                        "(no live clerk threaded into this surface)",
                    ),
                }
            }
            ModeCard::Debugger => match state.debugger {
                // The debugger re-executes the threaded turn against the LIVE World (the same
                // `debug::render` the gpui panel calls), so the step list / refusal / witness
                // are the live truth, never a stale snapshot.
                Some(dbg) => debugger_view(&crate::debug::render(world, dbg.turn, dbg.breakpoints)),
                None => empty_state_view("🔬 The debugger", "(no turn threaded into this surface)"),
            },
            ModeCard::Replay => match state.replay {
                // The replay model is the VERIFIED reconstruction at the threaded cursor over
                // the live World's recorded history (the same `ReplayPanelModel::build` the
                // gpui panel calls), so scrubbing reflects live.
                Some(rp) => {
                    let history = world.recorded_turns();
                    replay_view(&crate::replay::ReplayPanelModel::build(
                        history, rp.cursor, rp.fork,
                    ))
                }
                None => {
                    empty_state_view("⟲ Replay", "(no replay cursor threaded into this surface)")
                }
            },
            ModeCard::Swarm => match state.swarm {
                // The swarm coordinator is cockpit-side state (NOT the ledger), threaded through
                // `state.swarm`. The survey (members · inboxes · activity · budget) is built off
                // it live; the killer-demo headline is appended when its script is booted. Absent
                // (a stateless/default build) → an honest empty state, never a fabricated roster.
                Some(sw) => {
                    let view = crate::swarm::SwarmView::build(sw.swarm, world);
                    swarm_view(&view, sw.demo, sw.demo_lines)
                }
                None => empty_state_view(
                    "⛂ The swarm",
                    "(no live swarm coordinator threaded into this surface)",
                ),
            },
            ModeCard::ServiceExplorer => {
                // The focused cell's DERIVED service interface as the viewer sees it (a pure
                // function of the live World + focus — the same `ServiceExplorer::build` the gpui
                // panel consumes). Read-only: the genuine method invoke stays in the gpui panel.
                let se = crate::service_explorer::ServiceExplorer::build(
                    world,
                    focus,
                    focus,
                    viewer.clone(),
                );
                service_explorer_view(&se)
            }
            ModeCard::Powerbox => {
                // The CapDesk designation surface over the focused cell as the granter: the picker
                // of GRANTABLE targets is read live off `focus`'s c-list (`mint_needs_held_factory`
                // made visible — a thing the granter does not hold never appears). A standing app
                // request stands in for a launched app's real `CapabilityRequest`. Read-only: the
                // genuine attenuated grant turn stays in the gpui panel.
                let request = crate::powerbox::CapabilityRequest::new(
                    focus,
                    "a confined app would reach one peer/resource — designate exactly one",
                    AuthRequired::None,
                );
                let pb = crate::powerbox::Powerbox::present(world, focus, &request);
                powerbox_view(&pb)
            }
        }
    }
}

/// A `text` leaf node (the card vocabulary's label).
fn card_text(s: impl Into<String>) -> ViewTree {
    ViewTree::Text {
        props: TextProps { text: s.into() },
    }
}

/// A colored status `pill` (badge) node.
fn card_pill(s: impl Into<String>, tag: &str) -> ViewTree {
    ViewTree::Pill {
        props: PillProps {
            text: s.into(),
            tag: tag.to_string(),
        },
    }
}

/// A titled `section` container node.
fn card_section(title: impl Into<String>, children: Vec<ViewTree>) -> ViewTree {
    ViewTree::Section {
        props: SectionProps {
            title: title.into(),
            tag: String::new(),
            adept: false,
        },
        children,
    }
}

/// An **adept-only** `section` (progressive disclosure) — the "see the bones" drawer the
/// clean newcomer projection ([`deos_view::disclose`] at [`deos_view::Disclosure::Simple`],
/// which the card mount paints) DROPS and an adept REVEALS. Raw hashes / interface ids / the
/// "this is a verified turn" mechanics a stranger does not need go here.
fn card_section_adept(title: impl Into<String>, children: Vec<ViewTree>) -> ViewTree {
    ViewTree::Section {
        props: SectionProps {
            title: title.into(),
            tag: String::new(),
            adept: true,
        },
        children,
    }
}

/// A horizontal `row` node.
fn card_row(children: Vec<ViewTree>) -> ViewTree {
    ViewTree::Row { children }
}

/// A wrapping spatial `grid` node (`cols` cells per row; 0 → free wrap).
fn card_grid(cols: usize, children: Vec<ViewTree>) -> ViewTree {
    ViewTree::Grid {
        props: GridProps { cols },
        children,
    }
}

/// A glyph `icon` node, tinted by a semantic palette `tag`.
fn card_icon(glyph: impl Into<String>, tag: &str) -> ViewTree {
    ViewTree::Icon {
        props: IconProps {
            glyph: glyph.into(),
            tag: tag.to_string(),
        },
    }
}

/// A `button` node firing affordance `turn` with `arg` (a cap-gated verified turn).
fn card_button(label: impl Into<String>, turn: impl Into<String>, arg: i64) -> ViewTree {
    ViewTree::Button {
        props: ButtonProps {
            label: label.into(),
            on_click: OnClick {
                turn: turn.into(),
                arg,
            },
        },
    }
}

/// The WONDER ROOM as a portable card — the 1999-AOL front door. Every ledger cell is a tile
/// in a spatial `grid`; its glow `icon` (✦ alive / ○ quiet) is a LIVE projection of the recent
/// dynamics stream; each tile carries a `look` button. A pure function of the live World
/// (`WonderRoom::build`). Read-mostly: the drag-value grab/drop conserving turn stays in the
/// gpui room (the same read-only-card / live-action-in-gpui posture as the directory card).
fn wonder_view(room: &WonderRoom) -> ViewTree {
    let glowing = room.cells.iter().filter(|c| c.is_glowing()).count();
    let mut tiles: Vec<ViewTree> = Vec::new();
    for gc in &room.cells {
        let short = crate::reflect::short_hex(gc.cell.as_bytes());
        let (glyph, tag) = if gc.is_glowing() {
            ("✦", "good")
        } else {
            ("○", "muted")
        };
        // A warm description of what the cell holds (an issuer well carries −supply — named
        // as a wellspring, never a scary negative).
        let holds = if gc.balance < 0 {
            format!("a wellspring (−{})", gc.balance.unsigned_abs())
        } else {
            format!("holds {}", gc.balance)
        };
        // A warm liveliness read — "just stirred" for a cell the recent stream touched,
        // "resting" for a quiet one. No jargon; a child reads the glow, an adept the count.
        let pulse = if gc.is_glowing() {
            card_pill(
                if gc.recent_touches > 1 {
                    "alive · just stirred".to_string()
                } else {
                    "alive".to_string()
                },
                "good",
            )
        } else {
            card_pill("resting".to_string(), "muted")
        };
        tiles.push(card_section(
            "",
            vec![
                card_row(vec![card_icon(glyph, tag), card_text(short.clone())]),
                card_text(holds),
                pulse,
                card_button("look", format!("inspect:{short}"), 1),
            ],
        ));
    }
    if tiles.is_empty() {
        tiles.push(card_text("The room is empty — nothing has been made yet."));
    }
    ViewTree::VStack {
        children: vec![
            card_text("✦ The room — poke the glowing things. Nothing here can break."),
            card_pill(
                format!("{} thing(s) · {glowing} glowing", room.cells.len()),
                "accent",
            ),
            card_grid(4, tiles),
        ],
    }
}

/// A small "nothing threaded here" placeholder (an honest empty state, never fabricated
/// data) for a stateful card built without its cockpit-side [`SurfaceState`] (the default
/// stateless mount, e.g. the bake).
fn empty_state_view(title: &str, note: &str) -> ViewTree {
    ViewTree::VStack {
        children: vec![card_text(title.to_string()), card_text(note.to_string())],
    }
}

/// Render one uniform reflective [`crate::reflect::Inspectable`] as a card section: a title
/// line, its friendly scalar fields up front, the raw ids/hashes tucked into an adept drawer.
fn inspectable_card(obj: &crate::reflect::Inspectable) -> ViewTree {
    let mut friendly: Vec<ViewTree> = Vec::new();
    let mut raw: Vec<ViewTree> = Vec::new();
    for f in &obj.fields {
        let row = card_text(format!("{}: {}", f.key, field_value_display(&f.value)));
        match f.value {
            FieldValue::Id(_) | FieldValue::Hash(_) => raw.push(row),
            _ => friendly.push(row),
        }
    }
    let mut children = Vec::new();
    if obj.subtitle.is_empty() {
        children.push(card_text(obj.title.clone()));
    } else {
        children.push(card_text(format!("{} · {}", obj.title, obj.subtitle)));
    }
    children.extend(friendly);
    if !raw.is_empty() {
        children.push(card_section_adept("raw ids", raw));
    }
    card_section("", children)
}

/// THE CIPHERCLERK vault as a portable card — the live HD-identity roster, the capability
/// tokens those identities hold, and the recipient-targeted delegations, each a uniform
/// reflective object. A pure function of the live `Cipherclerk` (cockpit-side state threaded
/// through [`SurfaceState::clerk`]), so a mint/attenuate/delegate the operator just fired
/// shows live. Read-only (the genuine crypto loop stays in the gpui panel).
fn cipherclerk_view(panel: &crate::cipherclerk::CipherclerkPanel) -> ViewTree {
    let section_or_note =
        |items: &[crate::reflect::Inspectable], title: &str, empty: &str| -> ViewTree {
            let rows: Vec<ViewTree> = if items.is_empty() {
                vec![card_text(empty.to_string())]
            } else {
                items.iter().map(inspectable_card).collect()
            };
            card_section(title, rows)
        };
    ViewTree::VStack {
        children: vec![
            card_text("⚷ The cipherclerk — your signing identities and the caps they hold"),
            card_row(vec![
                card_pill(
                    format!(
                        "{} identit{}",
                        panel.identities.len(),
                        if panel.identities.len() == 1 {
                            "y"
                        } else {
                            "ies"
                        }
                    ),
                    "accent",
                ),
                card_pill(format!("{} token(s)", panel.tokens.len()), "good"),
                card_pill(
                    format!("{} delegation(s)", panel.delegations.len()),
                    "accent",
                ),
            ]),
            section_or_note(
                &panel.identities,
                "who you can act as",
                "(no identities yet — mint one in the clerk panel)",
            ),
            section_or_note(
                &panel.tokens,
                "capability tokens you hold",
                "(no tokens minted yet)",
            ),
            section_or_note(
                &panel.delegations,
                "capabilities handed to others",
                "(no delegations yet)",
            ),
        ],
    }
}

/// THE STEP-DEBUGGER as a portable card — the turn under the lens re-executed against the
/// live World, its per-effect step list (conservation deltas, the break/refusal markers), the
/// refusal explanation (THE prize) or the conserving-commit line, and the witness inspection
/// tucked into an adept drawer. A pure function of the live [`crate::debug::DebuggerPanel`]
/// (built from the cockpit-threaded turn + breakpoints), so it tracks the operator's lens.
fn debugger_view(panel: &crate::debug::DebuggerPanel) -> ViewTree {
    let mut steps: Vec<ViewTree> = Vec::new();
    for s in &panel.steps {
        let (glyph, tag) = if !s.committed {
            ("✗", "bad")
        } else if s.is_break {
            ("◆", "warn")
        } else {
            ("·", "muted")
        };
        steps.push(card_row(vec![
            card_icon(glyph, tag),
            card_text(format!("k{} {}", s.index, s.label)),
            card_pill(format!("Σδ={}", s.conservation_delta), tag),
        ]));
    }
    if steps.is_empty() {
        steps.push(card_text("(the turn has no steps)".to_string()));
    }
    let verdict = match &panel.refusal {
        Some(r) => card_section(
            "what happened",
            vec![
                card_pill(format!("REFUSED · guard: {}", r.guard), "bad"),
                card_text(r.headline.clone()),
                card_section_adept("why", vec![card_text(r.detail.clone())]),
            ],
        ),
        None => card_row(vec![card_pill(
            format!(
                "COMMITS · final Σδ = {} (conserves)",
                panel.final_conservation_delta
            ),
            "good",
        )]),
    };
    let w = &panel.witness;
    let witness = card_section_adept(
        "under the hood",
        vec![
            card_text(format!("conservation proof: {}", w.has_conservation_proof)),
            card_text(format!("execution proof: {}", w.has_execution_proof)),
            card_text(format!("witness blobs: {}", w.witness_blob_count)),
            card_text(format!("binding proofs: {}", w.binding_proof_count)),
        ],
    );
    ViewTree::VStack {
        children: vec![
            card_text(format!("🔬 {}", panel.title)),
            card_text(panel.subtitle.clone()),
            card_section("steps", steps),
            verdict,
            witness,
        ],
    }
}

/// THE REPLAY / TIME-TRAVEL scrubber as a portable card — the recorded history timeline (the
/// cursor's landing marked), the VERIFIED reconstruction at the cursor (root-checked; a
/// mismatch surfaced as a red pill), the prev-step diff (what the cursor's turn did), and a
/// pinned what-if fork's divergence. A pure function of the live
/// [`crate::replay::ReplayPanelModel`] (built at the cockpit-threaded cursor over the live
/// World's recorded history), so scrubbing reflects live.
fn replay_view(model: &crate::replay::ReplayPanelModel) -> ViewTree {
    // The timeline — every recorded landing point; the cursor's step marked.
    let mut timeline: Vec<ViewTree> = Vec::new();
    for e in &model.timeline {
        let here = e.step == model.cursor;
        let (glyph, tag) = if here {
            ("▶", "good")
        } else {
            ("·", "muted")
        };
        timeline.push(card_row(vec![
            card_icon(glyph, tag),
            card_text(format!("step {} · {}", e.step, e.label)),
        ]));
    }
    if timeline.is_empty() {
        timeline.push(card_text("(no history yet)".to_string()));
    }
    // The VERIFIED reconstruction at the cursor.
    let cs = &model.cursor_state;
    let mut cursor_rows: Vec<ViewTree> = vec![card_row(vec![
        card_text(format!("reconstructed at step {}", cs.step)),
        if cs.root_verified {
            card_pill("root verified", "good")
        } else {
            card_pill("ROOT MISMATCH", "bad")
        },
    ])];
    for (id, bal, caps) in &cs.cells {
        cursor_rows.push(card_text(format!(
            "{} · balance {} · {} cap(s)",
            crate::reflect::short_hex(id.as_bytes()),
            bal,
            caps
        )));
    }
    cursor_rows.push(card_section_adept(
        "root",
        vec![card_text(format!(
            "root {}",
            crate::reflect::short_hex(&cs.root)
        ))],
    ));
    let mut children = vec![
        card_text(
            "⟲ Replay — scrub history; every landing is re-derived from genesis and root-checked",
        ),
        card_pill(format!("cursor at step {}", model.cursor), "accent"),
        card_section("timeline", timeline),
        card_section("reconstructed state (verified)", cursor_rows),
    ];
    // The prev-step diff (what the cursor's turn did).
    if let Some(diff) = &model.diff_from_prev {
        let rows: Vec<ViewTree> = if diff.is_empty() {
            vec![card_text("(no change)".to_string())]
        } else {
            diff.changes
                .iter()
                .map(|(_, c)| card_text(c.label()))
                .collect()
        };
        children.push(card_section("what this step did", rows));
    }
    // A pinned what-if fork's divergence.
    if let Some(fork) = &model.fork {
        let mut rows = vec![card_row(vec![
            card_text(format!("forked at step {}", fork.branch_step)),
            if fork.committed {
                card_pill("committed", "good")
            } else {
                card_pill("refused", "bad")
            },
            if fork.diverged {
                card_pill("diverged", "warn")
            } else {
                card_pill("identical", "muted")
            },
        ])];
        for (_, c) in &fork.divergence.changes {
            rows.push(card_text(c.label()));
        }
        children.push(card_section("what-if fork", rows));
    }
    ViewTree::VStack { children }
}

/// THE A2 SWARM as a portable card — N agent cells coordinating as cap-confined Surface cells.
/// The header strip (members · committed actions · pending wakes · aggregate budget), one section
/// per member (backing/balance/action-count/inbox + per-member budget meter), the killer-demo (N5
/// pug-handoff) frame/budget headline + its captured transcript when the script is booted, and the
/// activity feed of executor receipts + inter-member notify edges. A pure function of the live
/// [`crate::swarm::SwarmView`] (built off the cockpit-threaded coordinator), so it tracks every
/// emit/drain. Read-only (the genuine emit/drain/transfer turns stay in the gpui panel).
fn swarm_view(
    view: &crate::swarm::SwarmView,
    demo: Option<&crate::demo::HeadlineDemo>,
    demo_lines: &[String],
) -> ViewTree {
    let mut children: Vec<ViewTree> = vec![card_text(
        "⛂ The swarm — agents coordinating as cap-confined cells. Every action is a receipted turn.",
    )];

    // The header strip — swarm-wide counts + the conserved aggregate budget over bounded members.
    let mut header = vec![
        card_pill(format!("{} member(s)", view.members.len()), "accent"),
        card_pill(format!("{} action(s)", view.total_actions), "good"),
        card_pill(
            format!("{} pending wake(s)", view.total_pending),
            if view.total_pending > 0 {
                "warn"
            } else {
                "muted"
            },
        ),
    ];
    if view.budget.bounded_members > 0 {
        header.push(card_pill(
            format!(
                "budget {}/{} computrons",
                view.budget.total_spent, view.budget.total_ceiling
            ),
            "accent",
        ));
    }
    children.push(card_row(header));

    // One section per member: a status row (live/unbacked · balance · actions · inbox · budget)
    // followed by the member's inbox of pending/drained notify edges.
    let mut member_sections: Vec<ViewTree> = Vec::new();
    for m in &view.members {
        let (glyph, gtag) = if m.backed {
            ("●", "good")
        } else {
            ("○", "bad")
        };
        let mut status = vec![
            card_icon(glyph, gtag),
            card_text(format!("{} · {}", m.name, m.short)),
            card_pill(if m.backed { "live" } else { "UNBACKED" }, gtag),
            card_pill(format!("bal {}", m.balance), "muted"),
            card_pill(format!("{} action(s)", m.action_count), "good"),
            card_pill(
                format!("{} pending", m.pending_notify),
                if m.pending_notify > 0 {
                    "warn"
                } else {
                    "muted"
                },
            ),
        ];
        if let Some(ceiling) = m.budget.ceiling {
            status.push(card_pill(
                format!("{}/{} cmp", m.budget.spent, ceiling),
                if m.budget.is_exhausted() {
                    "bad"
                } else {
                    "accent"
                },
            ));
        }
        let mut entry = vec![card_row(status)];
        for n in &m.inbox {
            let (mark, mtag) = if n.drained {
                ("✓", "muted")
            } else {
                ("⚡", "warn")
            };
            entry.push(card_row(vec![card_icon(mark, mtag), card_text(n.label())]));
        }
        member_sections.push(card_section("", entry));
    }
    if member_sections.is_empty() {
        member_sections.push(card_text("(no members yet — boot the swarm to coordinate)"));
    }
    children.push(card_section(
        "members (cap-confined, mandate-gated)",
        member_sections,
    ));

    // THE KILLER DEMO (N5 pug-handoff) headline + captured transcript, when the script is booted.
    if let Some(d) = demo {
        let mut demo_hdr = vec![card_pill(
            format!(
                "frame {}/{}",
                d.cursor(),
                crate::demo::HeadlineDemo::TOTAL_STEPS
            ),
            "accent",
        )];
        match d.next_step_label() {
            Some(label) => demo_hdr.push(card_pill(format!("next: {label}"), "warn")),
            None => demo_hdr.push(card_pill("script complete", "good")),
        }
        if let Some(v) = d.swarm().stingray_view() {
            demo_hdr.push(card_pill(
                format!("budget {}/{} computrons", v.total_drawn, v.ceiling),
                if v.exhausted { "bad" } else { "good" },
            ));
        }
        let mut demo_kids = vec![card_row(demo_hdr)];
        if demo_lines.is_empty() {
            demo_kids.push(card_text(
                "(press ▶ next frame, or ⏩ run all, in the swarm panel to drive the script)",
            ));
        } else {
            for line in demo_lines {
                // A refusal line is the teaching moment (warn); the executor's reason sub-lines
                // (indented) are muted. We split multi-line entries so each row is one line.
                let is_refusal = line.contains("REFUSED");
                for (i, sub) in line.lines().enumerate() {
                    let tag = if is_refusal && i == 0 {
                        "warn"
                    } else {
                        "muted"
                    };
                    demo_kids.push(card_row(vec![card_pill(sub.trim_end().to_string(), tag)]));
                }
            }
        }
        children.push(card_section(
            "⚑ the killer demo (N5) · the pug-handoff evaluation artifact",
            demo_kids,
        ));
    }

    // The activity feed — recent committed/refused actions with their height + notify edges.
    let mut feed: Vec<ViewTree> = Vec::new();
    for e in &view.activity {
        let (mark, mtag) = if e.committed {
            ("✓", "good")
        } else {
            ("✗", "bad")
        };
        let h = e
            .height
            .map(|h| format!("h{h}"))
            .unwrap_or_else(|| "—".to_string());
        let mut rows = vec![card_row(vec![
            card_icon(mark, mtag),
            card_text(format!("{h} · {} · {}", e.member_short, e.summary)),
        ])];
        for edge in &e.notify_edges {
            rows.push(card_row(vec![
                card_icon("→", "accent"),
                card_text(edge.clone()),
            ]));
        }
        feed.push(card_section("", rows));
    }
    if feed.is_empty() {
        feed.push(card_text(
            "(no swarm actions yet — use the panel's verbs to run the first turns)",
        ));
    }
    children.push(card_section(
        "activity feed (executor receipts · notify edges)",
        feed,
    ));

    ViewTree::VStack { children }
}

/// THE SERVICE EXPLORER as a portable card — a focused cell's DERIVED service interface as the
/// viewer sees it: a summary pill row + one row per declared method (name · arity · auth tier ·
/// replayable/serviced semantics · the cap badge `authorized`). A pure function of the live
/// [`crate::service_explorer::ServiceExplorer`] (built off the live World + focus). Read-only: the
/// genuine method invocation (a real verified turn) stays in the gpui panel.
fn service_explorer_view(se: &crate::service_explorer::ServiceExplorer) -> ViewTree {
    let authorized = se.methods.iter().filter(|m| m.authorized).count();
    let mut rows: Vec<ViewTree> = Vec::new();
    if se.methods.is_empty() {
        rows.push(card_text(
            "(this cell publishes no methods — its program dispatches on no method symbol)",
        ));
    }
    for m in &se.methods {
        let semantics = if m.is_invokable() {
            "replayable"
        } else {
            "serviced (named OFE seam)"
        };
        let arity = match m.arity {
            Some(n) => format!("{n} arg(s)"),
            None => "variadic".to_string(),
        };
        let mut r = vec![
            card_icon(
                if m.authorized { "🔓" } else { "🔒" },
                if m.authorized { "good" } else { "muted" },
            ),
            card_text(format!("{} · {} · {}", m.name, arity, semantics)),
        ];
        r.push(card_pill(
            format!("needs {:?}", m.required),
            if m.authorized { "good" } else { "warn" },
        ));
        r.push(card_section_adept(
            "symbol",
            vec![card_text(format!(
                "0x{}",
                crate::reflect::short_hex(&m.symbol)
            ))],
        ));
        rows.push(card_row(r));
    }
    ViewTree::VStack {
        children: vec![
            card_text("📐 What this cell can do — its service interface"),
            card_row(vec![
                card_pill(format!("{} method(s)", se.methods.len()), "accent"),
                card_pill(format!("{authorized} you may call"), "good"),
            ]),
            card_section("methods (cap-annotated for you)", rows),
            card_section_adept(
                "interface id",
                vec![card_text(format!(
                    "interface 0x{}",
                    crate::reflect::short_hex(&se.interface_id)
                ))],
            ),
        ],
    }
}

/// THE POWERBOX / CapDesk as a portable card — the focused cell as the granter, a standing app
/// request, and the picker of GRANTABLE targets (every cell the granter actually holds a cap
/// reaching, read live off its c-list — `mint_needs_held_factory` made visible: a thing the granter
/// does not hold never appears, so the user can only ever designate from their own authority). A
/// pure function of the live [`crate::powerbox::Powerbox`]. Read-only: the genuine attenuated grant
/// turn stays in the gpui panel.
fn powerbox_view(pb: &crate::powerbox::Powerbox) -> ViewTree {
    let mut targets: Vec<ViewTree> = Vec::new();
    if pb.grantable.is_empty() {
        targets.push(card_text(
            "(you hold no caps reaching another cell — nothing to designate. The powerbox is \
             not ambient: it can only offer your own authority.)",
        ));
    }
    for g in &pb.grantable {
        targets.push(card_row(vec![
            card_icon("⬡", "accent"),
            card_text(format!("{} (you may hand this app)", g.label)),
            card_pill(format!("ceiling {:?}", g.held_rights), "good"),
        ]));
    }
    ViewTree::VStack {
        children: vec![
            card_text("🗝 The powerbox — hand a confined app exactly one capability, narrowed."),
            card_row(vec![
                card_pill(
                    format!(
                        "granter {}",
                        crate::reflect::short_hex(pb.principal.as_bytes())
                    ),
                    "accent",
                ),
                card_pill(
                    format!("{} grantable target(s)", pb.grantable.len()),
                    "good",
                ),
            ]),
            card_section(
                "the app's request",
                vec![
                    card_text(pb.reason.clone()),
                    card_pill(
                        format!(
                            "asks for {:?} (a ceiling, not a command)",
                            pb.desired_rights
                        ),
                        "warn",
                    ),
                ],
            ),
            card_section("what you can designate (your own authority)", targets),
        ],
    }
}

/// The SERVICE DIRECTORY as a portable card — a summary pill row + one row per discovered
/// service. Read-only (the genuine announce is a real verified turn in the gpui panel).
fn service_directory_view(dir: &ServiceDirectory) -> ViewTree {
    let mut rows: Vec<ViewTree> = Vec::new();
    if dir.services.is_empty() {
        rows.push(card_text(
            "(no service-publishing cells in this image — a cell publishes an interface \
             when its program dispatches on a method symbol)",
        ));
    }
    for s in &dir.services {
        let kind = match s.kind {
            ServiceKind::Service => "service",
            ServiceKind::Capability => "capability",
        };
        // The friendly line up front; the interface-id hex tucked into the adept drawer.
        let mut r = vec![card_text(format!(
            "⬡ {} · {} · {} thing(s) it can do",
            s.label, kind, s.method_count,
        ))];
        if s.announced {
            r.push(card_pill("listed", "good"));
        }
        r.push(card_section_adept(
            "id",
            vec![card_text(format!(
                "interface {}",
                crate::reflect::short_hex(&s.interface_id)
            ))],
        ));
        rows.push(card_row(r));
    }
    ViewTree::VStack {
        children: vec![
            card_text("📇 What's on offer in here"),
            card_row(vec![
                card_pill(format!("{} service(s)", dir.services.len()), "accent"),
                card_pill(format!("{} listed", dir.announced_count), "good"),
            ]),
            card_section("things you can use", rows),
        ],
    }
}

/// The dregg:// WEB-OF-CELLS as a portable card — one row per addressable cell (its uri +
/// preview + an attested/unverified badge), drawn off the real attested fetch. Read-only.
fn web_cells_view(browser: &WebCellsBrowser) -> ViewTree {
    let mut rows: Vec<ViewTree> = Vec::new();
    if browser.cells.is_empty() {
        rows.push(card_text("(no addressable cells in this image)"));
    }
    for c in &browser.cells {
        rows.push(card_row(vec![
            card_text(format!("🔗 {} · {}", c.uri, c.preview)),
            if c.attested {
                card_pill("attested", "good")
            } else {
                card_pill("unverified", "warn")
            },
        ]));
    }
    ViewTree::VStack {
        children: vec![
            card_text("🌐 Pages you can open in here"),
            card_pill(format!("{} page(s)", browser.cells.len()), "accent"),
            card_section("places to go", rows),
        ],
    }
}

/// The human-layer TRUST surface as a portable card — the identity card (devices/guardians
/// as labeled rows), the recovery gauge, and the KEL timeline. All real projections.
fn trust_view(panel: &TrustPanel) -> ViewTree {
    let card = panel.identity_card();
    // Friendly identity rows up front; the raw key/hash fields tucked into an adept drawer.
    let mut id_rows: Vec<ViewTree> = Vec::new();
    let mut raw_id_rows: Vec<ViewTree> = Vec::new();
    for f in &card.fields {
        let row = card_text(format!("{}: {}", f.key, field_value_display(&f.value)));
        match f.value {
            FieldValue::Id(_) | FieldValue::Hash(_) => raw_id_rows.push(row),
            _ => id_rows.push(row),
        }
    }
    if !raw_id_rows.is_empty() {
        id_rows.push(card_section_adept("keys", raw_id_rows));
    }

    let mut recovery: Vec<ViewTree> = Vec::new();
    match panel.recovery_gauge() {
        Some(g) => recovery.push(card_text(format!(
            "{}: {}{}",
            g.label,
            g.value,
            g.ceiling.map(|c| format!(" / {c}")).unwrap_or_default(),
        ))),
        None => recovery.push(card_text("(no recovery in progress)")),
    }

    let kel = panel.kel_timeline();
    let kel_rows: Vec<ViewTree> = kel
        .events
        .iter()
        .map(|e| card_text(format!("h{} · {}", e.at, e.label)))
        .collect();

    ViewTree::VStack {
        children: vec![
            card_text(format!("⚷ Who you are · {}", panel.summary())),
            card_section("you", id_rows),
            card_section("getting back in", recovery),
            card_section("your history", kel_rows),
        ],
    }
}

/// Flatten a reflected [`FieldValue`] to a compact display string for a card `text` row.
fn field_value_display(v: &FieldValue) -> String {
    match v {
        FieldValue::Text(s) => s.clone(),
        FieldValue::Balance(n) => n.to_string(),
        FieldValue::Count(n) => n.to_string(),
        FieldValue::Bool(b) => b.to_string(),
        FieldValue::Id(b) | FieldValue::Hash(b) => crate::reflect::short_hex(b),
        FieldValue::CapEdge { target, slot } => {
            format!("→ {} @{}", crate::reflect::short_hex(target), slot)
        }
        FieldValue::FieldSlot { index, hex } => format!("[{index}] {hex}"),
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
///
/// This is the STATELESS mount (the reflective survey cards): it delegates to
/// [`build_mode_card_surface_with_state`] with an empty [`SurfaceState`], so the existing
/// cards build byte-identically. A stateful card (cipherclerk / debugger / replay) is built
/// through the `_with_state` entry, threading the live cockpit state so it renders the SAME
/// live state its gpui panel shows (no staleness).
#[allow(clippy::result_large_err)]
pub fn build_mode_card_surface(
    id: u64,
    kind: ModeCard,
    world: Rc<RefCell<World>>,
    focus: CellId,
    held: AuthRequired,
    cx: &mut App,
) -> Result<ModeCardSurface, String> {
    build_mode_card_surface_with_state(id, kind, world, focus, held, &SurfaceState::default(), cx)
}

/// **Mount a landed card as a cockpit mode's main-pane surface, threading the live
/// cockpit-side [`SurfaceState`]** — the stateful generalization of
/// [`build_mode_card_surface`]. Identical machinery (the view-tree is generated in Rust,
/// bridged to a [`ViewNode`], hosted as a [`CardPane`] over an applet attached to the live
/// `World`, and adopted as an editable view document), but the view-tree is generated WITH
/// `state`, so a stateful card (cipherclerk / debugger / replay) reflects the operator's live
/// cockpit state rather than a fabricated/stale snapshot. The stateless cards pass an empty
/// `state` and are unaffected.
#[allow(clippy::result_large_err)]
pub fn build_mode_card_surface_with_state(
    id: u64,
    kind: ModeCard,
    world: Rc<RefCell<World>>,
    focus: CellId,
    held: AuthRequired,
    state: &SurfaceState,
    cx: &mut App,
) -> Result<ModeCardSurface, String> {
    // The card's affordance surface over the focused cell: `bump` (Signature — held,
    // admitted) advances a state slot so a fired button visibly moves a bound row. The
    // fire commits THROUGH `World::commit_turn` onto the live ledger.
    let affordances = vec![("bump".to_string(), AuthRequired::Signature)];

    // GENERATE the card's view-tree from the live ledger + the threaded cockpit state BEFORE
    // attaching (the builder reads the World through a shared borrow; the attach takes the
    // `Rc` next).
    let tree_doc: ViewTree = {
        let w = world.borrow();
        kind.view_tree(&w, focus, &held, state)
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
        ModeCard::ServiceDirectory => 0xD1,
        ModeCard::WebCells => 0x7B,
        ModeCard::Trust => 0x7E,
        ModeCard::Wonder => 0x77,
        ModeCard::Cipherclerk => 0xCC,
        ModeCard::Debugger => 0xDB,
        ModeCard::Replay => 0x4E,
        ModeCard::Swarm => 0x52,
        ModeCard::ServiceExplorer => 0x5E,
        ModeCard::Powerbox => 0xB0,
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

// ===========================================================================
// THE CHAT CARD — chat-as-a-card mounted as a dock surface (the view-mount that
// discharges WEB-DEOS.md's "chat backend wasm-reachable, view-mounts pending").
//
// `deos_matrix::chat_card::ChatCard` is the gpui-free logic core (room = a
// RoomCell, timeline = the cell's turn history read back, send = a real turn via
// `ChatSource::send_turn`); `deos_matrix::chat_view::chat_view` is its
// renderer-independent `deos.ui.*` projection. THIS mount is the same shape as
// the composer/app-card mounts (projection → `deos_view::parse_view_tree` →
// `ViewNode` → `CardPane` → `CockpitSurface`), with one crucial difference the
// standard mode-card mount cannot express: the card's substance routes the
// composer input's `CHAT_SEND_TURN` fire to the REAL `ChatSource::send_turn`
// (the send↔turn weldpoint), not to a counter applet's affordance registry.
// ===========================================================================

/// **The chat card's live substance** — the [`CardSubstance`] backing a mounted
/// chat card renders over. Reads answer from the REAL room cell (`get_u64` is the
/// cell's live `turn_count`; `receipt_count` is the same count as the audit-tape
/// watermark, so own sends AND foreign messages both advance it), the composer
/// draft lives here as ephemeral view-state (NEVER cell state), and
/// [`CardSubstance::fire`] routes [`CHAT_SEND_TURN`] to [`ChatCard::send`] — ONE
/// real verified turn against the room cell, leaving a [`deos_matrix::SendReceipt`].
///
/// The native renderer's `input` is display/agent-driven (deos-view's honest
/// parity boundary), so the draft is seeded through [`Self::set_draft`] (the
/// agent/test path today; the web renderer's editable field is live).
pub struct ChatCardSubstance {
    chat: ChatCard,
    /// The composer's ephemeral draft (the `CHAT_DRAFT_KEY` view-state).
    draft: String,
    /// The receipt the LAST send left (turn index + post-root) — the honest "it
    /// really committed" read a host/test inspects after a fire.
    last_receipt: Option<deos_matrix::SendReceipt>,
}

impl ChatCardSubstance {
    /// Wrap a chat card as a live card substance.
    pub fn new(chat: ChatCard) -> Self {
        ChatCardSubstance {
            chat,
            draft: String::new(),
            last_receipt: None,
        }
    }

    /// Seed the composer draft (the agent/test path — the native `input` is
    /// display-only, so the draft arrives here rather than from a keystroke).
    pub fn set_draft(&mut self, draft: impl Into<String>) {
        self.draft = draft.into();
    }

    /// The chat card this substance drives (for re-projection / inspection).
    pub fn chat(&self) -> &ChatCard {
        &self.chat
    }

    /// The receipt the last send left, if any (turn index + post-root).
    pub fn last_receipt(&self) -> Option<&deos_matrix::SendReceipt> {
        self.last_receipt.as_ref()
    }
}

impl CardSubstance for ChatCardSubstance {
    fn cell(&self) -> CellId {
        // The room cell IS the card's sovereign cell — the same 32 bytes the chat
        // side derives (`deos_matrix::CellId` is the bytes; here they name the
        // bind source the pane's signal registry keys on).
        CellId(self.chat.room().cell_id.0)
    }

    fn receipt_count(&self) -> usize {
        // The room cell's live turn count is the honest audit-tape watermark: a
        // send through THIS substance moves it, and so does a foreign message
        // (both conservatively caught up by the pulse; never under-invalidating).
        self.chat.room().turn_count as usize
    }

    fn get_u64(&self, slot: usize) -> u64 {
        // The chat card's one bound scalar: the room cell's live turn count.
        if slot == CHAT_TURNS_SLOT {
            self.chat.room().turn_count
        } else {
            0
        }
    }

    fn get_view(&self, key: &str) -> Option<String> {
        (key == CHAT_DRAFT_KEY).then(|| self.draft.clone())
    }

    fn fire(&mut self, method: &str, _arg: i64) -> Result<(), String> {
        // THE SEND↔TURN ROUTE: the composer input's submit fires CHAT_SEND_TURN;
        // the draft (ephemeral view-state) becomes the body of ONE real verified
        // turn against the room cell via `ChatSource::send_turn`. An empty draft
        // or an unknown affordance is refused in-band — no turn, no receipt.
        if method != CHAT_SEND_TURN {
            return Err(format!("chat card: unknown affordance '{method}'"));
        }
        let body = self.draft.trim().to_string();
        if body.is_empty() {
            return Err("chat card: empty draft — nothing to send".to_string());
        }
        let receipt = self.chat.send(&body).map_err(|e| e.to_string())?;
        self.last_receipt = Some(receipt);
        self.draft.clear();
        Ok(())
    }
}

/// The chat card mounted as a [`CockpitSurface`] — the [`CardPane`] gpui entity
/// (the same renderer every other card mounts through) over the shared
/// [`ChatCardSubstance`] (the real room cell the rendered widgets read + fire).
pub struct ChatCardSurface {
    id: SurfaceId,
    entity: Entity<CardPane>,
    substance: Rc<RefCell<ChatCardSubstance>>,
    focus: FocusHandle,
}

/// **Mount the chat card as a dock surface** — the same mount shape as the
/// composer card ([`ModeCard::Composer`] via the card mounts above): generate the
/// renderer-independent view-tree (here `deos_matrix::chat_view`'s `deos.ui.*`
/// JSON), bridge it through the canonical [`deos_view::parse_view_tree`], and
/// host the resulting [`CardPane`] — except the substance routes the composer's
/// [`CHAT_SEND_TURN`] to the REAL [`deos_matrix::ChatSource::send_turn`].
///
/// `chat` is an opened [`ChatCard`] over whichever [`deos_matrix::ChatSource`]
/// the cockpit holds (the seeded `MockSource` offline, the live comms-PD source
/// wired). A build error is returned for the caller to surface fail-soft.
#[allow(clippy::result_large_err)]
pub fn build_chat_card_surface(
    id: u64,
    chat: ChatCard,
    cx: &mut App,
) -> Result<ChatCardSurface, String> {
    // Project the card's live state to the renderer-independent view-tree and
    // bridge it into the renderer's `ViewNode` (the same JSON every renderer —
    // native / web / discord / seL4 viewer — parses).
    let json = chat_view_json(&chat);
    let tree: ViewNode = deos_view::parse_view_tree(&json)
        .map_err(|e| format!("chat card view-tree bridge: {e}"))?;

    let room = chat.room();
    let title = format!(
        "chat · {} — live room cell ({})",
        room.room_id,
        chat.backend_label()
    );

    // Share the substance so the rendered input/binds and the host drive the SAME
    // room cell (one live object).
    let substance = Rc::new(RefCell::new(ChatCardSubstance::new(chat)));
    let sub_dyn: CardSubstanceRef = substance.clone();
    let entity = cx.new(|_cx| CardPane::new_substance(sub_dyn, tree, title));

    Ok(ChatCardSurface {
        id: SurfaceId(id),
        entity,
        substance,
        focus: cx.focus_handle(),
    })
}

impl ChatCardSurface {
    /// The shared chat substance (so a host/agent can seed the draft, fire the
    /// send, and read the last receipt — the SAME backing the widgets drive).
    pub fn substance(&self) -> Rc<RefCell<ChatCardSubstance>> {
        self.substance.clone()
    }

    /// The [`CardPane`] gpui entity (for a host that mounts the card body directly).
    pub fn entity_handle(&self) -> Entity<CardPane> {
        self.entity.clone()
    }

    /// **Re-project the view from the live room cell** — the timeline rows are
    /// static projections (not binds), so after a send (or a foreign message
    /// arriving on the room cell) the host calls this to regenerate the
    /// `deos.ui.*` tree off the live card and swap it into the pane (the same
    /// re-bridge + [`CardPane::set_tree`] route [`ModeCardSurface::edit_view`]
    /// uses). The substance is untouched — only the view is refreshed.
    pub fn refresh_view<T: 'static>(&self, cx: &mut Context<T>) -> Result<(), String> {
        let json = chat_view_json(self.substance.borrow().chat());
        let tree: ViewNode = deos_view::parse_view_tree(&json)
            .map_err(|e| format!("chat card view-tree re-bridge: {e}"))?;
        self.entity.update(cx, |card, cx| {
            card.set_tree(tree);
            cx.notify();
        });
        Ok(())
    }
}

impl CockpitSurface for ChatCardSurface {
    fn item_id(&self) -> SurfaceId {
        self.id
    }

    fn tab_label(&self) -> SharedString {
        SharedString::from("chat")
    }

    fn render_body(&mut self, _window: &mut Window, cx: &mut App) -> AnyElement {
        // Immediate-mode binds re-read the live room cell at render time, so a
        // notify each frame keeps the bound turn count current after a send
        // (mirrors `CardSurface`).
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
        Box::new(ChatCardSurface {
            id: self.id,
            entity: self.entity.clone(),
            substance: self.substance.clone(),
            focus: self.focus.clone(),
        })
    }
}

// ===========================================================================
// TESTS — the stateful cards render LIVE state, not stale data. The honesty
// claim: a carded surface reflects the SAME live cockpit state its gpui panel
// shows. These exercise the pure view-builders over the render-models (the same
// models the gpui panels consume), proving that a change in the threaded state
// changes the rendered view-tree (no staleness) and that the absent-state mount
// is an honest empty state, never fabricated data.
// ===========================================================================
#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::CellId;

    /// CIPHERCLERK: a fresh clerk and a clerk with one identity render DIFFERENT cards —
    /// the live roster is reflected, not a stale/empty snapshot.
    #[test]
    fn cipherclerk_card_tracks_live_identities() {
        let empty = crate::cipherclerk::Cipherclerk::new();
        let empty_json = cipherclerk_view(&crate::cipherclerk::render(&empty)).to_json();
        assert!(empty_json.contains("0 identit"));

        let mut clerk = crate::cipherclerk::Cipherclerk::new();
        clerk.create_identity("alice", "dns", 7);
        let one_json = cipherclerk_view(&crate::cipherclerk::render(&clerk)).to_json();
        assert!(one_json.contains("1 identit"));
        assert!(one_json.contains("alice") || one_json.contains("who you can act as"));
        assert_ne!(
            empty_json, one_json,
            "the clerk card must reflect the live roster"
        );
    }

    /// REPLAY: moving the scrubber cursor renders a different card (the cursor's verified
    /// reconstruction is live, not pinned to genesis).
    #[test]
    fn replay_card_tracks_live_cursor() {
        let mk = |cursor: usize, verified: bool| crate::replay::ReplayPanelModel {
            timeline: vec![
                crate::replay::TimelineEntry {
                    step: 0,
                    root: [0u8; 32],
                    label: "genesis (empty)".to_string(),
                },
                crate::replay::TimelineEntry {
                    step: 1,
                    root: [1u8; 32],
                    label: "transfer".to_string(),
                },
            ],
            cursor,
            cursor_state: crate::replay::CursorState {
                step: cursor,
                root: [cursor as u8; 32],
                root_verified: verified,
                cells: vec![(CellId([2u8; 32]), 100, 1)],
            },
            diff_from_prev: None,
            fork: None,
        };
        let at0 = replay_view(&mk(0, true)).to_json();
        let at1 = replay_view(&mk(1, true)).to_json();
        assert!(at0.contains("cursor at step 0"));
        assert!(at1.contains("cursor at step 1"));
        assert_ne!(at0, at1, "the replay card must track the live cursor");

        // A failed root tooth surfaces honestly (a red mismatch pill), never silently.
        let bad = replay_view(&mk(1, false)).to_json();
        assert!(bad.contains("ROOT MISMATCH"));
    }

    /// DEBUGGER: a committing turn and a refused turn render different verdicts — the live
    /// re-execution's outcome is reflected (the refusal explanation is the prize).
    #[test]
    fn debugger_card_tracks_live_verdict() {
        let witness = crate::debug::WitnessInspection {
            has_conservation_proof: true,
            has_execution_proof: true,
            witness_blob_count: 2,
            binding_proof_count: 1,
            public_inputs: None,
        };
        let commits = crate::debug::DebuggerPanel {
            title: "transfer".to_string(),
            subtitle: "commits".to_string(),
            steps: vec![crate::debug::StepRow {
                index: 0,
                label: "Transfer".to_string(),
                conservation_delta: 0,
                committed: true,
                is_break: false,
            }],
            current_state: Vec::new(),
            final_conservation_delta: 0,
            breakpoints: Vec::new(),
            break_hit: None,
            refusal: None,
            witness: witness.clone(),
        };
        let refused = crate::debug::DebuggerPanel {
            title: "over-spend".to_string(),
            subtitle: "refused".to_string(),
            steps: vec![crate::debug::StepRow {
                index: 0,
                label: "Transfer".to_string(),
                conservation_delta: -5,
                committed: false,
                is_break: true,
            }],
            current_state: Vec::new(),
            final_conservation_delta: -5,
            breakpoints: Vec::new(),
            break_hit: Some(0),
            refusal: Some(crate::debug::RefusalRender {
                guard: "Conservation".to_string(),
                headline: "value would not conserve".to_string(),
                detail: "Σδ = -5 at effect 0".to_string(),
                effect_index: Some(0),
                cells: Vec::new(),
            }),
            witness,
        };
        let ok = debugger_view(&commits).to_json();
        let no = debugger_view(&refused).to_json();
        assert!(ok.contains("COMMITS"));
        assert!(no.contains("REFUSED"));
        assert_ne!(
            ok, no,
            "the debugger card must reflect the live re-execution verdict"
        );
    }

    /// The absent-state mount (a stateless/default build, e.g. the bake) is an HONEST empty
    /// state — never fabricated data.
    #[test]
    fn stateful_cards_absent_state_is_honest() {
        let json = empty_state_view("⚷ The cipherclerk", "(no live clerk threaded)").to_json();
        assert!(json.contains("no live clerk"));
    }

    /// SWARM: more committed actions / a pending wake render a DIFFERENT card — the live
    /// coordinator's counts are reflected, not a stale snapshot.
    #[test]
    fn swarm_card_tracks_live_members_and_actions() {
        use crate::swarm::{SwarmBudget, SwarmMemberView, SwarmView};
        let mk = |actions: usize, pending: usize| SwarmView {
            members: vec![SwarmMemberView {
                agent: CellId([3u8; 32]),
                short: "ab12".into(),
                name: "coordinator".into(),
                backed: true,
                balance: 100,
                action_count: actions,
                pending_notify: pending,
                inbox: Vec::new(),
                budget: crate::swarm::BudgetMeter {
                    spent: 0,
                    ceiling: None,
                },
            }],
            activity: Vec::new(),
            total_pending: pending,
            total_actions: actions,
            budget: SwarmBudget::default(),
        };
        let none = swarm_view(&mk(0, 0), None, &[]).to_json();
        let busy = swarm_view(&mk(2, 1), None, &[]).to_json();
        assert!(
            none.contains("0 action(s)"),
            "quiet swarm shows zero actions"
        );
        assert!(busy.contains("2 action(s)"));
        assert!(busy.contains("1 pending wake(s)"));
        assert!(busy.contains("coordinator"));
        assert_ne!(
            none, busy,
            "the swarm card must reflect the live action/pending counts"
        );
    }

    /// SERVICE EXPLORER: the method list reflects the cell's interface AND the per-method cap
    /// badge (authorized vs not), so the read-only card is anti-ghost (it shows the full
    /// interface and which calls the viewer may make).
    #[test]
    fn service_explorer_card_lists_methods_with_cap_badges() {
        use crate::service_explorer::{MethodEntry, ServiceExplorer};
        use dregg_cell::interface::Semantics;
        let se = ServiceExplorer {
            cell: CellId([1u8; 32]),
            viewer: CellId([1u8; 32]),
            viewer_rights: AuthRequired::Signature,
            interface_id: [9u8; 32],
            inspectable: None,
            methods: vec![
                MethodEntry {
                    name: "transfer".into(),
                    symbol: [2u8; 32],
                    arity: Some(1),
                    required: AuthRequired::Signature,
                    semantics: Semantics::Replayable,
                    authorized: true,
                },
                MethodEntry {
                    name: "admin".into(),
                    symbol: [3u8; 32],
                    arity: None,
                    required: AuthRequired::Proof,
                    semantics: Semantics::Serviced,
                    authorized: false,
                },
            ],
        };
        let json = service_explorer_view(&se).to_json();
        assert!(json.contains("transfer") && json.contains("admin"));
        assert!(json.contains("2 method(s)"));
        assert!(
            json.contains("1 you may call"),
            "the cap badge counts authorized methods"
        );
        assert!(
            json.contains("serviced"),
            "a serviced method is surfaced honestly"
        );
    }

    /// POWERBOX: the grantable-target picker is exactly the granter's reachable authority — a
    /// thing the granter holds appears; the card is a pure projection of the user's own caps.
    #[test]
    fn powerbox_card_shows_grantable_targets() {
        use crate::powerbox::{GrantableTarget, Powerbox};
        let pb = Powerbox {
            principal: CellId([1u8; 32]),
            app_cell: CellId([2u8; 32]),
            reason: "needs to reach one peer".into(),
            desired_rights: AuthRequired::None,
            grantable: vec![GrantableTarget {
                target: CellId([5u8; 32]),
                held_slot: 0,
                held_rights: AuthRequired::Signature,
                label: "cd34".into(),
            }],
        };
        let json = powerbox_view(&pb).to_json();
        assert!(json.contains("1 grantable target(s)"));
        assert!(json.contains("cd34"), "the held target is offered");
        assert!(
            json.contains("needs to reach one peer"),
            "the app's reason is shown"
        );

        // An empty c-list → nothing to designate (the powerbox is not ambient).
        let empty = Powerbox {
            grantable: Vec::new(),
            ..pb
        };
        let ejson = powerbox_view(&empty).to_json();
        assert!(ejson.contains("0 grantable target(s)"));
        assert!(ejson.contains("not ambient"));
    }

    /// CHAT: the mounted substance routes the composer's fire to the REAL
    /// `ChatSource::send_turn` — the draft becomes one verified turn on the room
    /// cell (timeline grows, receipt lands, draft clears), and an empty draft or an
    /// unknown affordance is refused in-band (no turn).
    #[test]
    fn chat_substance_routes_send_to_the_real_send_turn() {
        use deos_matrix::source::MockSource;
        use std::sync::Arc;

        let src: Arc<dyn deos_matrix::ChatSource> = Arc::new(MockSource::seeded());
        let room_id = src.rooms().unwrap()[0].room_id.to_string();
        let chat = ChatCard::open(src, room_id);
        let before = chat.timeline().unwrap().len();
        let turns_before = chat.room().turn_count;

        let mut sub = ChatCardSubstance::new(chat);
        assert_eq!(
            sub.get_u64(CHAT_TURNS_SLOT),
            turns_before,
            "the bound scalar is the room cell's live turn count"
        );

        // An empty draft is refused in-band — no turn, no receipt.
        assert!(sub.fire(CHAT_SEND_TURN, 0).is_err());
        assert!(sub.last_receipt().is_none());

        // An unknown affordance is refused in-band.
        sub.set_draft("hello from the cockpit mount");
        assert!(sub.fire("bump", 1).is_err());

        // The real route: draft → send_turn → one verified turn on the room cell.
        sub.fire(CHAT_SEND_TURN, 0)
            .expect("the send routes to the real send_turn");
        let receipt = sub.last_receipt().expect("the send left a receipt");
        assert_eq!(receipt.turn_index, turns_before + 1);
        assert_eq!(
            sub.get_view(CHAT_DRAFT_KEY).as_deref(),
            Some(""),
            "the draft cleared after the send"
        );
        let after = sub.chat().timeline().unwrap();
        assert_eq!(
            after.len(),
            before + 1,
            "the room cell's history grew by one"
        );
        assert_eq!(after.last().unwrap().body, "hello from the cockpit mount");
        assert_eq!(
            sub.receipt_count() as u64,
            turns_before + 1,
            "the watermark advanced with the turn"
        );
    }

    /// CHAT: the deos-matrix projection bridges through the SAME canonical parser
    /// every renderer uses — and the parsed tree carries the composer input bound
    /// to the send action id the substance routes.
    #[test]
    fn chat_card_json_bridges_to_the_renderer() {
        use deos_matrix::source::MockSource;
        use std::sync::Arc;

        fn find_input(node: &ViewNode) -> Option<(String, String)> {
            match node {
                ViewNode::Input {
                    bind_view,
                    fire_turn,
                    ..
                } => Some((bind_view.clone(), fire_turn.clone())),
                ViewNode::VStack(cs)
                | ViewNode::Row(cs)
                | ViewNode::List(cs)
                | ViewNode::Table(cs) => cs.iter().find_map(find_input),
                ViewNode::Section { children, .. } | ViewNode::Grid { children, .. } => {
                    children.iter().find_map(find_input)
                }
                _ => None,
            }
        }

        let src: Arc<dyn deos_matrix::ChatSource> = Arc::new(MockSource::seeded());
        let room_id = src.rooms().unwrap()[0].room_id.to_string();
        let chat = ChatCard::open(src, room_id);

        let json = chat_view_json(&chat);
        let tree = deos_view::parse_view_tree(&json)
            .expect("the chat projection parses through the canonical bridge");
        let (bind_view, fire_turn) =
            find_input(&tree).expect("the parsed tree carries the composer input");
        assert_eq!(bind_view, CHAT_DRAFT_KEY);
        assert_eq!(fire_turn, CHAT_SEND_TURN);
    }
}
