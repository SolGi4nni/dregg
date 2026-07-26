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

/// **How a chat transport DECORATES the one prose walk** — the two things that differ between a
/// plain-text channel and a channel with a parse mode, and nothing else.
///
/// ⚑ This exists so a transport that needs a MONOSPACE GUARANTEE for its board (see
/// [`ChatTextStyle::telegram_html`]) does not fork the walker to get it. A parse mode is
/// all-or-nothing per message on Telegram, so the moment ONE span is markup, EVERY other span
/// becomes user-influenced text the parser will read — which is why the escape hook is part of the
/// same style as the fence rather than a post-pass a caller can forget. There is no way to
/// post-process a finished plain string into this: the fence has to be interleaved with the walk,
/// and the escape must NOT touch the fence.
pub struct ChatTextStyle {
    /// Escape one run of CONTENT so the transport's parse mode cannot read markup in it. Identity
    /// for a plain-text channel.
    pub escape: fn(&str) -> String,
    /// Emitted, UNESCAPED, on its own line before a [`ViewNode::CoordGrid`]'s rows — the opening
    /// half of the monospace guarantee. Empty = no fence (a plain-text channel).
    pub grid_open: &'static str,
    /// The closing half of [`grid_open`](Self::grid_open).
    pub grid_close: &'static str,
}

impl ChatTextStyle {
    /// **Plain text, no parse mode** — the projection every caller had before styles existed, and
    /// what WeChat OA still sends. Escape is the identity and there is no fence, so
    /// [`render_text_styled`] with this style is byte-for-byte [`render_text`].
    pub const fn plain() -> ChatTextStyle {
        ChatTextStyle {
            escape: no_escape,
            grid_open: "",
            grid_close: "",
        }
    }

    /// **Telegram, `parse_mode: HTML`** — the board fenced in `<pre>` (Telegram renders a `pre`
    /// block in a MONOSPACE font; a `sendMessage` with no parse mode at all renders in a
    /// PROPORTIONAL one, where a grid of equal-character-count cells does not line up into
    /// columns), and every content run HTML-escaped because the parse mode is per-message.
    pub const fn telegram_html() -> ChatTextStyle {
        ChatTextStyle {
            escape: escape_telegram_html,
            grid_open: "<pre>",
            grid_close: "</pre>",
        }
    }
}

impl Default for ChatTextStyle {
    fn default() -> Self {
        Self::plain()
    }
}

fn no_escape(s: &str) -> String {
    s.to_string()
}

/// **Escape a run of text for Telegram's `HTML` parse mode** — the three characters its parser
/// reads (`&`, `<`, `>`), and no others. `&` FIRST, or the ampersands of the other two escapes get
/// escaped again.
///
/// Telegram's HTML mode is deliberately the narrowest parse mode it offers: MarkdownV2 would put
/// eighteen characters (`_*[]()~`>#+-=|{}.!`) into every label, prose line and identity on the
/// surface, and one unescaped `.` or `-` in a sentence fails the whole `sendMessage` with
/// `can't parse entities`. Three characters is a surface small enough to audit.
pub fn escape_telegram_html(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            other => out.push(other),
        }
    }
    out
}

/// **Render a [`ViewNode`] surface into chat message text** (the *non-affordance* half).
/// [`ViewNode::Menu`]/[`ViewNode::Button`] are OMITTED (they ride the channel's affordance carrier —
/// Telegram's inline keyboard, WeChat's numbered reply list — not the prose); section titles head
/// their blocks; text nodes are lines; a LITERAL [`ViewNode::Pill`] paints as a `[badge]`, and a
/// row of them as one line of badges. Trailing whitespace is trimmed.
pub fn render_text(tree: &ViewNode) -> String {
    render_text_styled(tree, &ChatTextStyle::plain())
}

/// [`render_text`] with a transport's [`ChatTextStyle`] — the SAME walk, escaped and fenced for a
/// channel that has a parse mode. `ChatTextStyle::plain()` is exactly [`render_text`].
pub fn render_text_styled(tree: &ViewNode, style: &ChatTextStyle) -> String {
    let mut out = String::new();
    walk(tree, 0, style, &mut out);
    out.trim_end().to_string()
}

fn walk(node: &ViewNode, depth: usize, style: &ChatTextStyle, out: &mut String) {
    match node {
        ViewNode::Text(t) => {
            if !t.trim().is_empty() {
                push_content(out, style, t.trim());
            }
        }
        ViewNode::Section {
            title, children, ..
        } => {
            if !title.trim().is_empty() {
                // A heading, kept as WORDS rather than markup: with a parse mode live, wrapping
                // this in `<b>` would put the transport's syntax into a string the game author
                // controls, for a visual the prose does not need.
                let heading = if depth == 0 {
                    title.trim().to_string()
                } else {
                    format!("— {}", title.trim())
                };
                push_content(out, style, &heading);
            }
            for c in children {
                walk(c, depth + 1, style, out);
            }
        }
        ViewNode::VStack(children) | ViewNode::List(children) => {
            for c in children {
                walk(c, depth, style, out);
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
                        flush_badges(&mut badges, style, out);
                        walk(c, depth, style, out);
                    }
                }
            }
            flush_badges(&mut badges, style, out);
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
                push_content(out, style, &badge(text));
            }
        }
        // The affordance half — rendered as the channel's affordance carrier, not as text.
        ViewNode::Menu { .. } | ViewNode::Button { .. } => {}
        // Full node coverage: the remaining containers recurse (an affordance/section nested in a
        // Table/Grid/Tabs/Host/Adept still contributes its text) rather than dropping silently.
        ViewNode::Table(children) | ViewNode::Grid { children, .. } => {
            for c in children {
                walk(c, depth, style, out);
            }
        }
        ViewNode::Tabs { panels, .. } => {
            for p in panels {
                walk(p, depth, style, out);
            }
        }
        ViewNode::Host { view: Some(v), .. } => walk(v, depth, style, out),
        // An unresolved mount has no subtree to contribute prose from.
        ViewNode::Host { view: None, .. } => {}
        ViewNode::Adept(inner) => walk(inner, depth, style, out),
        // A coordinate board contributes its text grid to the prose (roles bracketed per
        // [`crate::tree::coordgrid_legend`]); the clickable cells ride the channel's affordance
        // carrier (keyboard / numbered block).
        //
        // ⚑ FENCED, where the channel offers a fence. The grid's only claim to being a grid is that
        // every cell occupies the same number of CHARACTERS — which lines up into columns in a
        // monospace font and into nothing at all in a proportional one. The fence is the channel's
        // monospace guarantee ([`ChatTextStyle::grid_open`]); a channel with no parse mode emits
        // none and reads exactly as it did before.
        ViewNode::CoordGrid { cols, cells } => {
            let grid = crate::tree::coordgrid_text(*cols, cells);
            if !style.grid_open.is_empty() {
                push_raw(out, style.grid_open);
            }
            for line in grid.lines() {
                push_content(out, style, line);
            }
            if !style.grid_close.is_empty() {
                push_raw(out, style.grid_close);
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
            push_content(out, style, &crate::tree::progress_text(label, *value, *max));
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
fn flush_badges(badges: &mut Vec<&str>, style: &ChatTextStyle, out: &mut String) {
    if badges.is_empty() {
        return;
    }
    let line = badges
        .iter()
        .map(|b| badge(b))
        .collect::<Vec<_>>()
        .join(" ");
    push_content(out, style, &line);
    badges.clear();
}

/// Emit one line of CONTENT — escaped for the transport's parse mode. ⚑ Every line of the surface's
/// own words goes through here; the only thing that may reach [`push_raw`] is a fence this module
/// itself authored.
fn push_content(out: &mut String, style: &ChatTextStyle, line: &str) {
    push_raw(out, &(style.escape)(line));
}

fn push_raw(out: &mut String, line: &str) {
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
                        wants_text: false,
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

    /// ⚑ **THE BOARD IS FENCED AND THE PROSE IS ESCAPED, in one walk.** The regression this closes:
    /// a Telegram `sendMessage` with NO `parse_mode` is laid out in a proportional font, where a grid
    /// whose only claim to being a grid is equal character counts per cell does not line up into
    /// columns at all — every board on that surface was misaligned. The fence buys the monospace
    /// font, and the moment a parse mode is live EVERY other line is text the parser reads, which is
    /// why the escape travels with the fence in one [`ChatTextStyle`] rather than as a later pass.
    #[test]
    fn the_html_style_fences_the_board_and_escapes_the_prose() {
        let tree = ViewNode::Section {
            title: "a < b & c".into(),
            tag: String::new(),
            children: vec![
                ViewNode::Text("the automaton is <@> and it sees you".into()),
                ViewNode::CoordGrid {
                    cols: 2,
                    cells: vec![
                        cell("<", 0, false),
                        cell("A", 1, true),
                        cell("&", 2, false),
                        cell("R", 3, false),
                    ],
                },
            ],
        };
        // Written with explicit `\n` per literal so no source line carries meaningful trailing
        // whitespace: the grid's trailing pad IS part of the alignment being asserted.
        let expected = concat!(
            "a &lt; b &amp; c\n",
            "the automaton is &lt;@&gt; and it sees you\n",
            "<pre>\n",
            "   0  1 \n",
            "0  &lt; [A]\n",
            "1  &amp;  R \n",
            "</pre>",
        );
        assert_eq!(
            render_text_styled(&tree, &ChatTextStyle::telegram_html()),
            expected,
            "the fence is raw, every content line is escaped, and the axes are labelled"
        );
        // The PLAIN style is the projection every other channel still gets, byte for byte.
        assert_eq!(
            render_text_styled(&tree, &ChatTextStyle::plain()),
            render_text(&tree),
            "the default style is exactly the plain walk"
        );
        assert!(
            !render_text(&tree).contains("<pre>"),
            "a channel with no parse mode emits no fence: {}",
            render_text(&tree)
        );
    }

    fn cell(glyph: &str, arg: i64, highlight: bool) -> crate::tree::CoordCell {
        crate::tree::CoordCell {
            glyph: glyph.into(),
            tag: String::new(),
            turn: String::new(),
            arg,
            highlight,
        }
    }
}
