//! # deos-view — render a deos-js applet's view-tree, native (gpui) OR web (HTML).
//!
//! THE RENDERER EXTRACTION (mirroring the deos-reflect extraction ember asked for):
//! `deos-js` stays GPUI-FREE — it produces the serializable `deos.ui.*` view-tree
//! ([`tree::ViewNode`]) and drives the verified turns. `deos-view` holds the renderers
//! that turn that DATA into a surface.
//!
//! TWO RENDERERS, ONE VIEW-TREE — the card is renderer-INDEPENDENT:
//!
//! * **`native`** (default, feature-gated) — `ViewNode` → real gpui-component pixels:
//!     1. `bridge::build_live_view` runs an applet's JS in real SpiderMonkey, extracts
//!        its view-tree and hands back the live `Applet` paired with the parsed
//!        [`tree::ViewNode`].
//!     2. `render::AppletView` walks the tree into gpui widgets (`vstack→v_flex`,
//!        `button→Button`, `text→Label`, `bind→Label` re-read, …); a button's `on_click`
//!        fires a REAL cap-gated verified turn; a `bind` re-reads the live ledger.
//!     3. `faces::FacesView` renders the moldable `present()` faces through the SAME
//!        vocabulary; `headless` bakes any view to a PNG offscreen (the cockpit's path).
//!
//! * **`web`** (feature-gated, gpui-FREE + deos-js-FREE) — the IDENTICAL
//!     [`tree::ViewNode`] → an HTML/DOM string ([`web::render_card_document`]),
//!     node-for-node mirroring the gpui vocabulary, into a browser-loadable `.html`. This
//!     is the web-projection of the reflective cockpit: the SAME card paints in a browser,
//!     not just the native window. See the `web_render_card` example for the bake.

// The view-tree MODEL is renderer-independent (gpui-free serializable DATA): it is
// always compiled, under BOTH the `native` and `web` renderers.
pub mod tree;
pub use tree::{parse_view_tree, RawNode, RawProps, ViewNode};

// ── The NATIVE renderer: `ViewNode` → real gpui-component pixels (the heavy stack
//    + deos-js live verified turns). Gated on `native` so the `web` build stays tiny. ──
#[cfg(feature = "native")]
pub mod bridge;
#[cfg(feature = "native")]
pub mod faces;
#[cfg(feature = "native")]
pub mod headless;
#[cfg(feature = "native")]
pub mod render;

#[cfg(feature = "native")]
pub use bridge::{build_live_view, view_tree_key, LiveView};
#[cfg(feature = "native")]
pub use faces::FacesView;
#[cfg(feature = "native")]
pub use render::{AppletView, SharedApplet};

// ── The WEB renderer: the SAME `ViewNode` → an HTML/DOM string. gpui-free + deos-js-
//    free (only serde). This is the web-projection of the reflective cockpit — the
//    card paints in a browser, not just the native cockpit. ──
#[cfg(feature = "web")]
pub mod web;
#[cfg(feature = "web")]
pub use web::{render_card_document, render_card_live_document, render_html};
