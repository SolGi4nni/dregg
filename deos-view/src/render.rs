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
//! INVALIDATION — this slice is IMMEDIATE-MODE: a `bind` re-reads the model at render
//! time, so re-rendering after a turn shows the updated value. The fine-grained
//! dirty-set hook (re-render only the touched node off the `WorldEvent` dirty-set) goes
//! where [`AppletView::render`] walks the tree — a future slice keys each `bind`'s
//! re-read to the slot the last turn touched instead of redrawing the whole tree.

use std::cell::RefCell;
use std::rc::Rc;

use deos_js::applet::Applet;
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

/// The gpui view that renders a deos-js applet's view-tree. A real gpui `Render`
/// entity — open it in a (headless or windowed) window and it paints the widgets.
pub struct AppletView {
    /// The live applet (shared so button handlers can fire turns + binds can re-read).
    applet: SharedApplet,
    /// The extracted view-tree (the real `deos.ui.*` element-tree).
    tree: ViewNode,
}

impl AppletView {
    /// Build a view from a shared applet + its view-tree.
    pub fn new(applet: SharedApplet, tree: ViewNode) -> Self {
        Self { applet, tree }
    }

    /// The shared applet handle (for the caller to inspect receipts after a turn).
    pub fn applet(&self) -> SharedApplet {
        self.applet.clone()
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
                // THE SIGNAL BINDING — re-read the bound model slot off the LIVE ledger
                // (the same witnessed read the JS closure made). Immediate-mode: this
                // re-runs every render, so after a turn the new value shows.
                let value = self.applet.borrow().get_u64(*slot);
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
