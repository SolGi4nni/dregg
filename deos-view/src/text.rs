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
        // An unresolved mount has no subtree to contribute prose from.
        ViewNode::Host { view: None, .. } => {}
        ViewNode::Adept(inner) => walk(inner, depth, out),
        // A coordinate board contributes its text grid to the prose (a highlighted cell bracketed);
        // the clickable cells ride the channel's affordance carrier (keyboard / numbered block).
        ViewNode::CoordGrid { cols, cells } => {
            let grid = crate::tree::coordgrid_text(*cols, cells);
            for line in grid.lines() {
                push_line(out, line);
            }
        }
        // A LITERAL-valued meter (a light clock, a carry capacity, a guardian's vitality) DOES have
        // a plain-text form — `light ████████░░░░ 18/26` — because it carries its own numbers; it
        // needs no live ledger the way a `gauge` does. It used to fall into the silent set below,
        // so a game whose whole tension is a burning clock painted that clock on the web and NOTHING
        // on Telegram/WeChat. One shared projection ([`crate::tree::progress_text`]), so the bar is
        // the same bar on every channel.
        ViewNode::Progress { value, max, label } => {
            push_line(out, &crate::tree::progress_text(label, *value, *max));
        }
        // ── The remaining leaves contribute NO chat prose (this match is EXHAUSTIVE on purpose:
        //    a new `ViewNode` variant must fail to compile here until its prose projection is
        //    DECIDED, never dropped by a silent `_ => {}`). None of these carries an affordance —
        //    every affordance rides the channel's carrier (Telegram's inline keyboard / WeChat's
        //    numbered reply list) via [`crate::backend::actuations`], NOT the prose — so a chat
        //    surface legitimately omits their visual (a slider/pill/icon is a badge or control
        //    layer with no plain-text form, and a `bind`/`gauge`'s live value is not available on
        //    this bind-less walk — unlike `progress`, which carries its own numbers).
        //    Their actuation reach is proven separately by the cross-surface differential test. ──
        ViewNode::Bind { .. }
        | ViewNode::Input { .. }
        | ViewNode::Gauge { .. }
        | ViewNode::Divider
        | ViewNode::Breadcrumb { .. }
        | ViewNode::Pill { .. }
        | ViewNode::Icon { .. }
        | ViewNode::Halo { .. }
        | ViewNode::Slider { .. }
        | ViewNode::Toggle { .. }
        | ViewNode::Tile { .. } => {}
    }
}

fn push_line(out: &mut String, line: &str) {
    if !out.is_empty() {
        out.push('\n');
    }
    out.push_str(line);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tree::{MenuItem, ViewNode};

    /// A LITERAL meter reaches the prose channels. This is the regression: a game whose whole
    /// tension is a burning clock rendered that clock in HTML and NOTHING at all in a Telegram or
    /// WeChat message, because `progress` sat in the silent-leaf set beside the slot-bound `gauge`.
    #[test]
    fn a_literal_meter_paints_its_bar_in_prose() {
        let tree = ViewNode::Section {
            title: "Vitals".into(),
            tag: "accent".into(),
            children: vec![
                ViewNode::Progress {
                    value: 18,
                    max: 26,
                    label: "light   ".into(),
                },
                ViewNode::Progress {
                    value: 2,
                    max: 6,
                    label: "pack    ".into(),
                },
                // The affordance half still rides the channel's carrier, not the prose.
                ViewNode::Menu {
                    items: vec![MenuItem {
                        label: "Descend".into(),
                        turn: "delve".into(),
                        arg: 0,
                        enabled: true,
                    }],
                },
            ],
        };
        assert_eq!(
            render_text(&tree),
            "Vitals\nlight    ████████░░░░ 18/26\npack     ████░░░░░░░░ 2/6",
            "both meters paint, aligned, and the menu stays out of the prose"
        );
    }

    /// A slot-bound `gauge` still contributes nothing here — its value lives on a ledger this walk
    /// does not have, and painting a fabricated fill would be a lie. The DIFFERENCE from `progress`
    /// is the point: one carries its numbers, the other does not.
    #[test]
    fn a_slot_bound_gauge_still_paints_no_fabricated_fill() {
        let tree = ViewNode::Gauge {
            slot: 3,
            max: 26,
            label: "light".into(),
        };
        assert_eq!(render_text(&tree), "");
    }
}
