//! # deos-view — render a deos-js applet's view-tree into REAL gpui-component pixels.
//!
//! THE RENDERER EXTRACTION (mirroring the deos-reflect extraction ember asked for):
//! `deos-js` stays GPUI-FREE — it produces the serializable `deos.ui.*` view-tree and
//! drives the verified turns. `deos-view` holds ALL the gpui and turns that data into
//! pixels.
//!
//! The flow:
//!
//!   1. [`bridge::build_live_view`] runs a deos-js applet's JS in real SpiderMonkey,
//!      extracts its view-tree (the engine `JSON.stringify`s it and the bridge reads it
//!      back out of the applet's ephemeral view-state) and hands back the live
//!      [`deos_js::applet::Applet`] paired with the parsed [`tree::ViewNode`].
//!   2. [`render::AppletView`] walks that tree into real gpui-component widgets
//!      (`vstack→v_flex`, `button→Button`, `text→Label`, `bind→Label`re-read, …). A
//!      button's `on_click` fires the applet's affordance = a REAL cap-gated verified
//!      turn (a `TurnReceipt`); a `bind` re-reads the model off the live ledger.
//!   3. [`faces::FacesView`] renders the moldable `present()` faces through the SAME
//!      vocabulary (the §7 unification — inspector and custom view share widgets).
//!
//! [`headless`] bakes any `Render` view to a PNG offscreen (the same HeadlessAppContext
//! + offscreen-wgpu path the cockpit's `--render-cockpit` bake uses), so the whole flow
//! is provable by RUNNING + a captured frame, not merely by compiling.

pub mod bridge;
pub mod faces;
pub mod headless;
pub mod render;
pub mod tree;

pub use bridge::{build_live_view, view_tree_key, LiveView};
pub use faces::FacesView;
pub use render::{AppletView, SharedApplet};
pub use tree::{parse_view_tree, ViewNode};
