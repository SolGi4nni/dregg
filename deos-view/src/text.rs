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
/// their blocks; text nodes are lines; a LITERAL [`ViewNode::Pill`] paints as a `[badge]`, and a
/// row of them as one line of badges. Trailing whitespace is trimmed.
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
        ViewNode::VStack(children) | ViewNode::List(children) => {
            for c in children {
                walk(c, depth, out);
            }
        }
        // A ROW is where badges live — a phase ladder, a seat's standing, an item's rarity. Its
        // LITERAL pills are gathered onto ONE line (`[1 · SEAL] [2 · OPEN] [3 · RESOLVE]`) rather
        // than one line each, because a ladder read down a column is not a ladder. A row carrying
        // no pill walks exactly as before, byte for byte.
        ViewNode::Row(children) => {
            let mut badges: Vec<&str> = Vec::new();
            for c in children {
                match literal_pill(c) {
                    Some(text) => badges.push(text),
                    None => {
                        flush_badges(&mut badges, out);
                        walk(c, depth, out);
                    }
                }
            }
            flush_badges(&mut badges, out);
        }
        // ⚑ **A PILL CARRIES ITS OWN WORDS, so it reaches the prose.** This arm used to be in the
        // silent set below, and it was a real hole rather than a style choice: WHOSE TURN / WHAT
        // PHASE / WHAT WAS EARNED is carried by a pill on most surfaces, so a Telegram or WeChat
        // reader was served a page that had been stripped of its status line — 15 of the 23
        // catalog offerings, measured by `dreggnet-web/tests/catalog_flow_harness.rs`.
        //
        // The `progress`/`gauge` distinction decides the split, exactly as it does above: a
        // LITERAL pill (`slot: None`) carries its text and is projected; a SLOT-BOUND pill's shown
        // text is chosen by a [`PillCase`] against a live ledger value this bind-less walk does not
        // have, so painting its static fallback would assert a state that may not hold — that one
        // stays silent, like `gauge`.
        ViewNode::Pill { .. } => {
            if let Some(text) = literal_pill(node) {
                push_line(out, &badge(text));
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
        // a plain-text form — `light ██████████████████░░░░░░░░ 18/26`, one cell PER STEP while the
        // denominator is countable — because it carries its own numbers; it
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
        //    surface legitimately omits their visual (a slider/icon is a decoration or a control
        //    layer with no plain-text form, and a `bind`/`gauge`'s live value is not available on
        //    this bind-less walk — unlike `progress` and a literal `pill`, which carry their own).
        //    Their actuation reach is proven separately by the cross-surface differential test. ──
        ViewNode::Bind { .. }
        | ViewNode::Input { .. }
        | ViewNode::Gauge { .. }
        | ViewNode::Divider
        | ViewNode::Breadcrumb { .. }
        | ViewNode::Icon { .. }
        | ViewNode::Halo { .. }
        | ViewNode::Slider { .. }
        | ViewNode::Toggle { .. }
        | ViewNode::Tile { .. } => {}
    }
}

/// The text of a LITERAL pill — one whose words are its own, not a [`crate::tree::PillCase`]
/// selected against a live ledger value. `None` for anything else (including a slot-bound pill,
/// whose static text is only the fallback).
fn literal_pill(node: &ViewNode) -> Option<&str> {
    match node {
        ViewNode::Pill {
            text, slot: None, ..
        } if !text.trim().is_empty() => Some(text.trim()),
        _ => None,
    }
}

/// A badge, bracketed so a reader can tell a status chip from a sentence.
fn badge(text: &str) -> String {
    format!("[{text}]")
}

/// Emit a run of badges as one line, and clear the run.
fn flush_badges(badges: &mut Vec<&str>, out: &mut String) {
    if badges.is_empty() {
        return;
    }
    let line = badges
        .iter()
        .map(|b| badge(b))
        .collect::<Vec<_>>()
        .join(" ");
    push_line(out, &line);
    badges.clear();
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
        // Both meters are COUNTABLE (`max <= COUNTABLE_METER_MAX`), so each paints one cell per
        // step and the two TRACKS are different lengths — 26 cells against 6. That is the
        // information a shared fixed width destroyed: at 12 cells wide these read as
        // "eight-ish twelfths" and "four twelfths", two rough fractions, when what a player needs
        // is 18 breaths left and 2 things carried. The LABELS still align (their padding is
        // emitted verbatim), which is what makes the stack scannable.
        assert_eq!(
            render_text(&tree),
            "Vitals\nlight    ██████████████████░░░░░░░░ 18/26\npack     ██░░░░ 2/6",
            "both meters paint, labels aligned, and the menu stays out of the prose"
        );
    }

    /// **A pill's words reach the prose, and a ROW of them is one line.** The regression this
    /// closes: WHOSE TURN / WHAT PHASE is a pill on most surfaces, so a Telegram or WeChat reader
    /// was handed a page with its status line deleted — 15 of the 23 catalog offerings, measured by
    /// `dreggnet-web/tests/catalog_flow_harness.rs` (`prose-parity`).
    #[test]
    fn a_literal_pill_reaches_the_prose_and_a_ladder_is_one_line() {
        let tree = ViewNode::Section {
            title: "Where the turn stands".into(),
            tag: "accent".into(),
            children: vec![
                ViewNode::Row(vec![
                    pill("1 · SEAL", None),
                    pill("2 · OPEN", None),
                    pill("3 · RESOLVE", None),
                ]),
                ViewNode::Text("Seal a move — both seats commit before either opens.".into()),
                // A row that MIXES prose and badges keeps the prose on its own line.
                ViewNode::Row(vec![ViewNode::Text("seat A".into()), pill("to move", None)]),
            ],
        };
        assert_eq!(
            render_text(&tree),
            "Where the turn stands\n\
             [1 · SEAL] [2 · OPEN] [3 · RESOLVE]\n\
             Seal a move — both seats commit before either opens.\n\
             seat A\n\
             [to move]"
        );
    }

    /// A SLOT-BOUND pill still paints nothing — its shown text is chosen by a `PillCase` against a
    /// live ledger value this bind-less walk does not have, so its static text is a fallback and
    /// asserting it could state a phase that does not hold. Exactly the `progress`/`gauge` split.
    #[test]
    fn a_slot_bound_pill_paints_no_fabricated_status() {
        assert_eq!(render_text(&pill("IDLE", Some(3))), "");
    }

    fn pill(text: &str, slot: Option<usize>) -> ViewNode {
        ViewNode::Pill {
            text: text.into(),
            tag: String::new(),
            slot,
            cases: Vec::new(),
        }
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
