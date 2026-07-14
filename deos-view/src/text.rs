//! **The shared [`ViewNode`] → plain-text walk** — the *prose* projection of the one IR.
//!
//! Two chat transports need the SAME prose: a Telegram message (text + an inline keyboard) and a
//! WeChat OA message (text + a numbered reply list). Both project the view-tree's *content* half —
//! room prose, party state, section titles — and both carry the *affordance* half OUT of the text
//! (Telegram as the keyboard, WeChat as the numbered block). That shared half lives here, ONCE, so
//! the second chat backend is a codec + a numbered block, never a second subset walker (the
//! subsetting IS the evidence they diverged — `docs/SURFACE-ONE-GATE-FOUR-PLANES.md`, safe-move #2).
//!
//! [`crate::telegram::render_text`] IS this function (re-exported); [`crate::wechat::WeChatBackend`]
//! calls it for its prose. FULL node coverage: every container recurses (an affordance/section
//! nested in a `Table`/`Grid`/`Tabs`/`Host`/`Adept` still contributes its text) rather than dropping
//! silently.

use crate::tree::ViewNode;

/// **Render a [`ViewNode`] surface into chat message text** (the *non-affordance* half).
/// [`ViewNode::Menu`]/[`ViewNode::Button`] are OMITTED (they ride the channel's affordance carrier —
/// Telegram's inline keyboard, WeChat's numbered reply list — not the prose); section titles head
/// their blocks; text nodes are lines. Trailing whitespace is trimmed.
pub fn render_text(tree: &ViewNode) -> String {
    let mut out = String::new();
    walk(tree, 0, &mut out);
    out.trim_end().to_string()
}

fn walk(node: &ViewNode, depth: usize, out: &mut String) {
    match node {
        ViewNode::Text(t) => {
            if !t.trim().is_empty() {
                push_line(out, t.trim());
            }
        }
        ViewNode::Section {
            title, children, ..
        } => {
            if !title.trim().is_empty() {
                // A bold-ish heading (kept plain-text; a live bot could set MarkdownV2).
                let heading = if depth == 0 {
                    title.trim().to_string()
                } else {
                    format!("— {}", title.trim())
                };
                push_line(out, &heading);
            }
            for c in children {
                walk(c, depth + 1, out);
            }
        }
        ViewNode::VStack(children) | ViewNode::Row(children) | ViewNode::List(children) => {
            for c in children {
                walk(c, depth, out);
            }
        }
        // The affordance half — rendered as the channel's affordance carrier, not as text.
        ViewNode::Menu { .. } | ViewNode::Button { .. } => {}
        // Full node coverage: the remaining containers recurse (an affordance/section nested in a
        // Table/Grid/Tabs/Host/Adept still contributes its text) rather than dropping silently.
        ViewNode::Table(children) | ViewNode::Grid { children, .. } => {
            for c in children {
                walk(c, depth, out);
            }
        }
        ViewNode::Tabs { panels, .. } => {
            for p in panels {
                walk(p, depth, out);
            }
        }
        ViewNode::Host { view: Some(v), .. } => walk(v, depth, out),
        ViewNode::Adept(inner) => walk(inner, depth, out),
        // A coordinate board contributes its text grid to the prose (a highlighted cell bracketed);
        // the clickable cells ride the channel's affordance carrier (keyboard / numbered block).
        ViewNode::CoordGrid { cols, cells } => {
            let grid = crate::tree::coordgrid_text(*cols, cells);
            for line in grid.lines() {
                push_line(out, line);
            }
        }
        // The bound/indicator leaves have no plain-text projection here.
        _ => {}
    }
}

fn push_line(out: &mut String, line: &str) {
    if !out.is_empty() {
        out.push('\n');
    }
    out.push_str(line);
}
