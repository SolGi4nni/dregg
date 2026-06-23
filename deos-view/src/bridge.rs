//! The **bridge** — drive a deos-js applet in real SpiderMonkey, extract its view-tree.
//!
//! `deos-js` keeps the view-tree GPUI-FREE: it is a serializable element-tree the JS
//! engine builds with `deos.ui.*`. The only public way an `Applet` carries a string
//! back to Rust is its ephemeral view-state (`Applet::get_view`, a plain in-memory
//! map — NOT cell state, NEVER a turn). So the bridge:
//!
//!   1. installs the applet on the thread-local the natives drive ([`set_current_applet`]);
//!   2. evals a JS program that builds the view-tree with `deos.ui.*`, tags each
//!      `bind` node with the model slot it reads (the closure isn't serializable), and
//!      stashes `JSON.stringify(tree)` into ephemeral view-state via `app.view.set`;
//!   3. takes the applet back and reads that string out with `Applet::get_view`.
//!
//! The view-tree this yields is the REAL one the SpiderMonkey engine produced through
//! `deos.ui.*` — not a Rust re-authoring. Firing + re-reading then go straight through
//! the held [`Applet`] (a button's onClick is `Applet::fire` = a real verified turn;
//! a `bind` re-read is `Applet::get_u64` off the live ledger).

use deos_js::applet::Applet;
use deos_js::js::{set_current_applet, take_current_applet};
use deos_js::JsRuntime;

use crate::tree::{parse_view_tree, ViewNode};

/// The view-state key the bridge JS stashes the stringified view-tree under.
const VIEWTREE_KEY: &str = "__deos_view_tree";

/// A driven applet plus its extracted view-tree. The [`Applet`] is the live substance
/// (its `fire` is a real cap-gated verified turn; `get_u64` a witnessed read); the
/// [`ViewNode`] is the element-tree the JS engine produced, ready for the renderer.
pub struct LiveView {
    /// The live applet — the renderer's button handlers fire its affordances and its
    /// `bind` nodes re-read its model. Held mutably so a turn can commit.
    pub applet: Applet,
    /// The extracted view-tree (the real `deos.ui.*` element-tree).
    pub tree: ViewNode,
}

/// Build a [`LiveView`] by running `applet_js` against `applet` in real SpiderMonkey.
///
/// `applet_js` MUST, against the installed `app` handle, build a view-tree and stash
/// it: e.g.
///
/// ```js
/// var app = deos.applet({ affordances: ["inc"] });
/// var b = deos.ui.bind(function() { return app.get(0); });
/// b.props.slot = 0;                              // tag the slot (closure isn't serializable)
/// var tree = deos.ui.vstack(deos.ui.text("Counter"), b, deos.ui.button("+1","inc",1));
/// app.view.set("__deos_view_tree", JSON.stringify(tree));
/// ```
///
/// (The view-tree build commits NOTHING; only firing a button's handler does.)
pub fn build_live_view(
    rt: &mut JsRuntime,
    applet: Applet,
    applet_js: &str,
) -> Result<LiveView, String> {
    set_current_applet(applet);
    rt.eval(applet_js).map_err(|e| format!("applet eval: {e}"))?;
    let applet = take_current_applet().ok_or("applet vanished from the runtime")?;

    let json = applet
        .get_view(VIEWTREE_KEY)
        .ok_or_else(|| {
            format!("applet JS did not stash a view-tree under view-state '{VIEWTREE_KEY}'")
        })?
        .to_string();

    let tree = parse_view_tree(&json)?;
    Ok(LiveView { applet, tree })
}

/// The view-state key, exposed so a caller's JS can name it consistently.
pub fn view_tree_key() -> &'static str {
    VIEWTREE_KEY
}
