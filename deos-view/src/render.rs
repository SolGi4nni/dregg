//! The **renderer** — walk a deos-js view-tree into REAL gpui-component widgets.
//!
//! The vocabulary is gpui-component (the longbridge widget fork the cockpit uses):
//!
//!   - `vstack` → [`gpui_component::v_flex`]   `row` → [`gpui_component::h_flex`]
//!   - `text`   → [`gpui_component::label::Label`]
//!   - `bind`   → a [`Label`] re-read off the live applet ledger (the signal binding)
//!   - `button` → [`gpui_component::button::Button`] whose `on_click` fires the
//!                applet's affordance = a REAL cap-gated verified turn (a `TurnReceipt`)
//!   - `input`  → a bordered field showing the ephemeral view-state value
//!   - `list` / `table` → a `v_flex` of the child nodes
//!
//! The same vocabulary renders the moldable `present()` faces ([`crate::faces`]) — the
//! §7 unification (the inspector and the custom view share widgets).
//!
//! INVALIDATION — the **fine-grained signal hook** (the SolidJS-shaped re-render).
//!
//! The renderer welds [`deos_js::signals::BindingRegistry`] into the render path:
//!
//!   - At construction the tree is walked ONCE ([`bind_plan`]) and every `bind` node is
//!     assigned a monotonic [`BindingId`] + `register`ed on its `(cell, slot)` source in
//!     the registry. (The applet's cell is the sovereignty boundary, so every bind reads
//!     `(applet.cell(), slot)`.)
//!   - Each bind's live value is held in a small per-binding **value cache**. A `bind`
//!     node renders out of the cache — NOT a fresh `get_u64` every paint.
//!   - On a committed turn the caller folds the turn's touched `(cell, slot)`s through
//!     [`AppletView::on_committed_turn`]: the registry's [`BindingRegistry::invalidate`]
//!     returns EXACTLY the dirty bindings, and only those re-read the live ledger into
//!     the cache. Clean bindings keep their cached value untouched — a turn on slot A
//!     re-evaluates binding A and leaves binding B alone (the fine-grained win).
//!
//! The first paint is still immediate-mode (the cache fills lazily from the live ledger
//! the first time each bind renders), so an un-driven view is always correct; the
//! felt-liveness is the INCREMENTAL update path the committed turn drives. A bind whose
//! value did not change re-reads nothing; the [`AppletView::last_dirty`] instrumentation
//! exposes exactly which bindings the last turn re-evaluated (the test bar).

use std::cell::{Cell, RefCell};
use std::collections::BTreeMap;
use std::rc::Rc;

use deos_js::applet::Applet;
use deos_js::signals::{BindingId, BindingRegistry, SourceEvent, Slot};
use dregg_types::CellId;
use gpui::{
    div, px, App, ClickEvent, Context, FontWeight, IntoElement, ParentElement, Render, Styled,
    Window,
};
use gpui_component::button::{Button, ButtonVariants};
use gpui_component::label::Label;
use gpui_component::{h_flex, v_flex, ActiveTheme};

use crate::tree::ViewNode;

/// A shared, interior-mutable handle on the live applet. The renderer reads the model
/// through it (the `bind` re-read) and a button's `on_click` fires a turn through it
/// (a real verified turn). One handle, shared by every widget — the single sovereign
/// cell behind the whole applet view.
pub type SharedApplet = Rc<RefCell<Applet>>;

/// The slot a `bind` node reads, in tree-walk (pre-order) appearance — the renderer
/// mints one [`BindingId`] per `bind` node monotonically, paired with the model `Slot`
/// the node re-reads. The cell is constant (the applet's sovereign cell), so the source
/// each binding registers is `(applet.cell(), slot)`.
fn bind_plan(tree: &ViewNode, out: &mut Vec<Slot>) {
    match tree {
        ViewNode::Bind { slot, .. } => out.push(*slot),
        ViewNode::VStack(cs)
        | ViewNode::Row(cs)
        | ViewNode::List(cs)
        | ViewNode::Table(cs) => {
            for c in cs {
                bind_plan(c, out);
            }
        }
        // Leaves that hold no bind source.
        ViewNode::Text(_) | ViewNode::Button { .. } | ViewNode::Input { .. } => {}
    }
}

/// The gpui view that renders a deos-js applet's view-tree. A real gpui `Render`
/// entity — open it in a (headless or windowed) window and it paints the widgets.
///
/// FINE-GRAINED LIVENESS: the view owns a [`BindingRegistry`] (deos-js's reverse index
/// `(cell, slot) → bindings`) and a per-binding **value cache**. A `bind` renders out of
/// the cache; a committed turn invalidates ONLY the touched `(cell, slot)`'s bindings
/// (via [`AppletView::on_committed_turn`]) and re-reads only those into the cache.
pub struct AppletView {
    /// The live applet (shared so button handlers can fire turns + binds can re-read).
    applet: SharedApplet,
    /// The extracted view-tree (the real `deos.ui.*` element-tree).
    tree: ViewNode,
    /// The applet's sovereign cell — the constant cell every bind reads a slot of.
    cell: CellId,
    /// The reverse index `(cell, slot) → bindings`. Built once at construction by
    /// registering each `bind` node (in tree-walk order) on its source. OWNED here; the
    /// model lives in deos-js (`signals.rs`) — this is the renderer consuming it.
    registry: BindingRegistry,
    /// The Nth `bind` node (tree-walk order) is `BindingId(n)` reading slot `bind_slots[n]`.
    /// Render walks the tree in the same order and consumes ids from a counter so each
    /// `bind` paints out of `cache[BindingId(n)]`.
    bind_slots: Vec<Slot>,
    /// The fine-grained value cache: `binding → last-read live value`. A `bind` paints
    /// from here; only `invalidate`d bindings re-read (the rest keep their cached value).
    /// `RefCell` because `render`/`node` take `&self` but lazily fill the cache on first
    /// paint of each binding.
    cache: RefCell<BTreeMap<BindingId, u64>>,
    /// The id-counter render uses to map the Nth painted `bind` node to `BindingId(n)`.
    /// Reset at the top of each `render`. `Cell` for the same `&self`-walk reason.
    render_cursor: Cell<u64>,
    /// Instrumentation: the bindings the LAST `on_committed_turn` re-evaluated (the
    /// dirty set). Empty until a turn drives the view. The test bar reads this to prove
    /// a turn on slot A dirtied ONLY binding A.
    last_dirty: RefCell<Vec<BindingId>>,
}

impl AppletView {
    /// Build a view from a shared applet + its view-tree, registering every `bind` node
    /// on its `(cell, slot)` source in the signal registry (the fine-grained index).
    pub fn new(applet: SharedApplet, tree: ViewNode) -> Self {
        let cell = applet.borrow().cell();
        let mut bind_slots = Vec::new();
        bind_plan(&tree, &mut bind_slots);

        let mut registry = BindingRegistry::new();
        for (n, slot) in bind_slots.iter().enumerate() {
            registry.register(BindingId(n as u64), cell, *slot);
        }

        Self {
            applet,
            tree,
            cell,
            registry,
            bind_slots,
            cache: RefCell::new(BTreeMap::new()),
            render_cursor: Cell::new(0),
            last_dirty: RefCell::new(Vec::new()),
        }
    }

    /// The shared applet handle (for the caller to inspect receipts after a turn).
    pub fn applet(&self) -> SharedApplet {
        self.applet.clone()
    }

    /// THE FINE-GRAINED HOOK — fold a committed turn's touched slots through the registry
    /// and re-read ONLY the dirty bindings into the cache.
    ///
    /// `touched_slots` are the `(cell, slot)`s the turn wrote (the cockpit projects the
    /// turn's `WorldEvent`s into these; for the single-cell applet they are slots of the
    /// applet's own cell). Returns the dirty set — exactly the bindings whose painted
    /// value may have changed. A turn touching a slot no `bind` reads dirties nothing
    /// (the view stays still). Clean bindings keep their cached value — never re-read.
    pub fn on_committed_turn(&self, touched_slots: &[Slot]) -> Vec<BindingId> {
        let events: Vec<SourceEvent> = touched_slots
            .iter()
            .map(|s| SourceEvent::new(self.cell, *s))
            .collect();
        let dirty = self.registry.invalidate_all(events);

        // Re-read ONLY the dirty bindings off the live ledger into the cache (the
        // witnessed read the `bind` closure made). Clean bindings are untouched.
        {
            let app = self.applet.borrow();
            let mut cache = self.cache.borrow_mut();
            for b in &dirty {
                if let Some(v) = self.registry.reread(*b, |_cell, slot| app.get_u64(slot)) {
                    cache.insert(*b, v);
                }
            }
        }

        *self.last_dirty.borrow_mut() = dirty.clone();
        dirty
    }

    /// The bindings the last [`on_committed_turn`](Self::on_committed_turn) re-evaluated
    /// (instrumentation / the test bar). Empty before any turn drove the view.
    pub fn last_dirty(&self) -> Vec<BindingId> {
        self.last_dirty.borrow().clone()
    }

    /// The cached live value of a binding, if it has been read (lazily on first paint or
    /// by a committed-turn re-read). For tests / instrumentation.
    pub fn cached(&self, binding: BindingId) -> Option<u64> {
        self.cache.borrow().get(&binding).copied()
    }

    /// How many `bind` nodes the view registered (one [`BindingId`] each).
    pub fn binding_count(&self) -> usize {
        self.bind_slots.len()
    }

    /// The value the next-painted `bind` node should show: its cached value, filling the
    /// cache lazily off the live ledger on first paint. Advances the render cursor so the
    /// Nth `bind` node maps to `BindingId(n)`.
    fn next_bind_value(&self, slot: Slot) -> u64 {
        let n = self.render_cursor.get();
        self.render_cursor.set(n + 1);
        let id = BindingId(n);
        let mut cache = self.cache.borrow_mut();
        *cache
            .entry(id)
            .or_insert_with(|| self.applet.borrow().get_u64(slot))
    }

    /// Render one node into a gpui element. Recursive: containers render their
    /// children with the same vocabulary.
    fn node(&self, node: &ViewNode, _window: &mut Window, cx: &mut App) -> gpui::AnyElement {
        let theme_fg = cx.theme().foreground;
        match node {
            ViewNode::VStack(children) => {
                let mut col = v_flex().gap_2().p_3();
                for c in children {
                    col = col.child(self.node(c, _window, cx));
                }
                col.into_any_element()
            }
            ViewNode::Row(children) => {
                let mut row = h_flex().gap_2().items_center();
                for c in children {
                    row = row.child(self.node(c, _window, cx));
                }
                row.into_any_element()
            }
            ViewNode::Text(s) => Label::new(s.clone())
                .text_color(theme_fg)
                .into_any_element(),
            ViewNode::Bind { slot, label } => {
                // THE SIGNAL BINDING — paint out of the fine-grained value CACHE. The
                // cache fills lazily off the live ledger on first paint (the same
                // witnessed read the JS closure made), then is updated ONLY for the
                // bindings a committed turn `invalidate`s (see `on_committed_turn`). A
                // clean binding repaints its cached value without re-reading the ledger —
                // the SolidJS-shaped fine-grained re-render.
                let value = self.next_bind_value(*slot);
                let text = if label.is_empty() {
                    value.to_string()
                } else {
                    format!("{label}{value}")
                };
                Label::new(text)
                    .font_weight(FontWeight::BOLD)
                    .text_color(theme_fg)
                    .into_any_element()
            }
            ViewNode::Button { label, turn, arg } => {
                // THE REAL TURN — a button's onClick fires the applet's affordance =
                // ONE cap-gated verified turn (a `TurnReceipt`). The handler captures
                // the shared applet + the (turn, arg) from the view-tree.
                let applet = self.applet.clone();
                let turn = turn.clone();
                let arg = *arg;
                Button::new(("deos-aff", label_hash(label)))
                    .primary()
                    .label(label.clone())
                    .on_click(move |_ev: &ClickEvent, _window, _cx| {
                        // Fire the verified turn. A cap refusal / executor reject is
                        // surfaced to stderr (the screenshot stays honest); the model
                        // simply does not advance.
                        if let Err(e) = applet.borrow_mut().fire(&turn, arg) {
                            eprintln!("deos-view: affordance '{turn}' did not commit: {e}");
                        }
                    })
                    .into_any_element()
            }
            ViewNode::Input { bind_view } => {
                // The ephemeral view-state value (draft text) — NOT cell state, never a
                // turn. Rendered as a bordered field showing the current draft.
                let draft = self
                    .applet
                    .borrow()
                    .get_view(bind_view)
                    .unwrap_or("")
                    .to_string();
                h_flex()
                    .px_2()
                    .py_1()
                    .border_1()
                    .border_color(cx.theme().border)
                    .rounded(px(4.))
                    .child(Label::new(if draft.is_empty() {
                        format!("‹{bind_view}›")
                    } else {
                        draft
                    }))
                    .into_any_element()
            }
            ViewNode::List(items) => {
                let mut col = v_flex().gap_1();
                for it in items {
                    col = col.child(self.node(it, _window, cx));
                }
                col.into_any_element()
            }
            ViewNode::Table(rows) => {
                let mut col = v_flex().gap_1().border_1().border_color(cx.theme().border);
                for r in rows {
                    col = col.child(self.node(r, _window, cx));
                }
                col.into_any_element()
            }
        }
    }
}

impl Render for AppletView {
    fn render(&mut self, window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        // Reset the bind-id cursor so the Nth `bind` node painted this frame maps to
        // `BindingId(n)` (the same order `bind_plan` registered them in).
        self.render_cursor.set(0);
        let tree = self.tree.clone();
        // `Context<Self>` derefs to `App`; the node walker reads the theme + applet
        // through `&mut App`.
        let app: &mut App = cx;
        div()
            .size_full()
            .bg(app.theme().background)
            .text_color(app.theme().foreground)
            .child(self.node(&tree, window, app))
    }
}

/// A stable id salt for a button from its label (so two buttons in one tree differ).
fn label_hash(label: &str) -> u64 {
    let mut h: u64 = 1469598103934665603; // FNV-1a offset
    for b in label.bytes() {
        h ^= b as u64;
        h = h.wrapping_mul(1099511628211);
    }
    h
}
