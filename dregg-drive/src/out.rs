//! **The frame — one command's worth of "what a viewer would now see", model-legibly.**
//!
//! Every surface answers a command with the same three things, in the same order, under the
//! same delimiters:
//!
//! 1. **REPLY** — the direct answer the channel gives the actor (a Telegram
//!    `answerCallbackQuery` ack, an HTTP status line). Distinct from the surface itself.
//! 2. **PAINT** — every surface update the command caused, each labelled with *how* it
//!    arrived. On a chat surface `SEND #3` and `EDIT #3` are DIFFERENT EVENTS and the
//!    difference is load-bearing: an EDIT to a message that is far up the scrollback is
//!    invisible to the reader, which is exactly how a second `/offerings` came to produce
//!    no visible output at all. A frame with ZERO paints and no reply is flagged.
//! 3. **CONTROLS** — the offered affordances with their indices, labels, wire payloads, and
//!    whether they are pressable. An agent driving this needs to know what it CAN do next
//!    without guessing, and a label is *user-facing state*: a fog leak has hidden in a
//!    button label while the prose sections were correct.
//!
//! Then `PILLS`, and `NOTES` (the diagnostics — the actual output of the instrument).

use std::collections::BTreeSet;
use std::fmt::Write as _;

/// One offered affordance, as the surface itself published it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Control {
    /// The index the driver's `press <n>` refers to (position in the offered list).
    pub index: usize,
    /// What the control SAYS. User-facing state; diffed across viewers to catch label leaks.
    pub label: String,
    /// The affordance verb, when the surface publishes it in the clear.
    pub turn: String,
    /// The affordance argument, when the surface publishes it in the clear.
    pub arg: i64,
    /// Whether the surface rendered it pressable (the cap tooth shown, not hidden).
    pub enabled: bool,
    /// The EXACT payload a press sends — a Telegram `callback_data`, a web `turn=&arg=`.
    /// Kept verbatim so `stale` can replay a payload from an earlier frame byte-for-byte.
    pub wire: String,
}

/// How one surface update reached the viewer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PaintHow {
    /// A NEW message/page appeared where the viewer is looking.
    Fresh(String),
    /// An EXISTING message was rewritten in place. Invisible if it has scrolled away.
    InPlace(String),
    /// A read the viewer performed (a GET) — the web analogue of "look at the screen".
    Read(String),
}

impl PaintHow {
    fn head(&self) -> String {
        match self {
            PaintHow::Fresh(what) => format!("SEND  {what}"),
            PaintHow::InPlace(what) => {
                format!("EDIT  {what}   (in place — invisible if scrolled away)")
            }
            PaintHow::Read(what) => format!("READ  {what}"),
        }
    }
}

/// One surface update: how it arrived, and the exact body the viewer would see.
#[derive(Debug, Clone)]
pub struct Paint {
    /// How it arrived.
    pub how: PaintHow,
    /// The body as that surface would show it (Telegram message text; web visible text).
    pub body: String,
}

/// One command's complete result.
#[derive(Debug, Clone, Default)]
pub struct Frame {
    /// The command that produced this frame, verbatim.
    pub verb: String,
    /// The channel's direct answer to the actor, if any.
    pub reply: Option<String>,
    /// Every surface update this command caused, in order.
    pub paints: Vec<Paint>,
    /// The affordances now on offer.
    pub controls: Vec<Control>,
    /// The state pills / meters the surface's own projection produced.
    pub pills: Vec<String>,
    /// Diagnostics — what the instrument actually found.
    pub notes: Vec<String>,
}

impl Frame {
    /// A frame for `verb` with nothing in it yet.
    pub fn new(verb: impl Into<String>) -> Self {
        Frame {
            verb: verb.into(),
            ..Frame::default()
        }
    }

    /// A frame that is only a note — a refusal by the driver itself, never by a surface.
    pub fn driver_note(verb: impl Into<String>, note: impl Into<String>) -> Self {
        let mut f = Frame::new(verb);
        f.notes.push(note.into());
        f
    }

    /// Record a diagnostic.
    pub fn note(&mut self, note: impl Into<String>) {
        self.notes.push(note.into());
    }

    /// **The silence check** — a command that caused no paint AND no reply produced NOTHING a
    /// user could see. That is a defect on any surface, and it is the shape of the second
    /// `/offerings` that read as a dead bot. Called by every surface before returning.
    pub fn flag_silence(&mut self) {
        if self.paints.is_empty() && self.reply.is_none() {
            self.note(
                "⚠ NO VISIBLE OUTPUT — this command painted nothing and the channel said \
                 nothing. A user issuing it sees a dead surface.",
            );
        }
        if self.reply.is_none()
            && !self.paints.is_empty()
            && self
                .paints
                .iter()
                .all(|p| matches!(p.how, PaintHow::InPlace(_)))
        {
            self.note(
                "⚠ EDIT-ONLY OUTPUT — every update was an in-place rewrite and the channel \
                 said nothing. If that message has scrolled away the user sees a dead surface.",
            );
        }
    }

    /// The offered labels, as a set — the unit a viewer-switch diff compares.
    pub fn label_set(&self) -> BTreeSet<String> {
        self.controls.iter().map(|c| c.label.clone()).collect()
    }

    /// Render the frame for a human or a model to read.
    pub fn render(&self, seq: usize) -> String {
        let mut out = String::new();
        let _ = writeln!(
            out,
            "\n════ [{seq}] {} {}",
            self.verb,
            "═".repeat(64usize.saturating_sub(self.verb.chars().count()))
        );
        if let Some(reply) = &self.reply {
            let _ = writeln!(out, "── REPLY ──────────────────────────────────────");
            for line in reply.lines() {
                let _ = writeln!(out, "  {line}");
            }
        }
        if self.paints.is_empty() {
            let _ = writeln!(out, "── PAINT ──────────────────────────────────────");
            let _ = writeln!(out, "  (none)");
        }
        for (i, paint) in self.paints.iter().enumerate() {
            let _ = writeln!(
                out,
                "── PAINT {}/{} · {} ──",
                i + 1,
                self.paints.len(),
                paint.how.head()
            );
            let body = paint.body.trim_end();
            if body.is_empty() {
                let _ = writeln!(out, "  (empty body — the viewer sees a blank surface)");
            }
            for line in body.lines() {
                let _ = writeln!(out, "  │ {line}");
            }
        }
        let _ = writeln!(
            out,
            "── CONTROLS ({}) ───────────────────────────────",
            self.controls.len()
        );
        if self.controls.is_empty() {
            let _ = writeln!(
                out,
                "  (none offered — a terminal state, or a surface with nothing to press)"
            );
        }
        for c in &self.controls {
            let _ = writeln!(
                out,
                "  [{idx}] {mark} {label}\n        {turn}/{arg}  wire={wire}",
                idx = c.index,
                mark = if c.enabled { "·" } else { "✗" },
                label = c.label,
                turn = c.turn,
                arg = c.arg,
                wire = c.wire,
            );
        }
        if !self.pills.is_empty() {
            let _ = writeln!(out, "── PILLS/METERS ───────────────────────────────");
            for p in &self.pills {
                let _ = writeln!(out, "  {p}");
            }
        }
        if !self.notes.is_empty() {
            let _ = writeln!(out, "── NOTES ──────────────────────────────────────");
            for n in &self.notes {
                for (i, line) in n.lines().enumerate() {
                    let _ = writeln!(out, "  {}{line}", if i == 0 { "" } else { "  " });
                }
            }
        }
        out
    }
}

/// **The viewer-switch diff** — what changed in the OFFERED CONTROLS when only the person
/// looking changed. Nothing else moved, so every difference here is a per-viewer projection
/// decision, and a difference that reveals another player's state is a leak.
pub fn fog_diff(
    before_viewer: &str,
    before: &BTreeSet<String>,
    after_viewer: &str,
    after: &BTreeSet<String>,
) -> String {
    let gone: Vec<&String> = before.difference(after).collect();
    let new: Vec<&String> = after.difference(before).collect();
    let mut out = String::new();
    let _ = write!(
        out,
        "VIEWER SWITCH {before_viewer} → {after_viewer}: {} label(s) shared",
        before.intersection(after).count()
    );
    if gone.is_empty() && new.is_empty() {
        let _ = write!(
            out,
            "\n  IDENTICAL control labels. Either the offering has no per-viewer projection, \
             or it has one and it is not reaching the controls."
        );
        return out;
    }
    for g in gone {
        let _ = write!(out, "\n  −{before_viewer}-only: {g}");
    }
    for n in new {
        let _ = write!(out, "\n  +{after_viewer}-only: {n}");
    }
    out
}

/// Strip HTML to the text a reader would see: `<script>`/`<style>` contents dropped, tags
/// removed, whitespace collapsed per line. Deliberately dumb — it is a READER, not a parser.
pub fn visible_text(html: &str) -> String {
    let mut out = String::new();
    let mut rest = html;
    // Drop the two element bodies a reader never sees.
    //
    // ⚑ The subtlety this got WRONG once, and the reason it is spelled out: the closing tag must
    // be the one belonging to the OPENING tag that was found. A first pass searched for
    // `</script>` and fell back to `</style>`, so on a page whose `<style>` sits in the head and
    // whose `<script>` sits at the foot — i.e. every page here — the `<style>` cut skipped
    // forward to the LATER `</script>` and silently deleted the entire document body in between.
    // The frames it produced looked like one-line pages. A reader that eats what it is reading
    // will invent defects; this is why it is careful now.
    loop {
        let lower = rest.to_ascii_lowercase();
        let cut = [("<script", "</script>"), ("<style", "</style>")]
            .iter()
            .filter_map(|(open, close)| lower.find(open).map(|at| (at, *close)))
            .min_by_key(|(at, _)| *at);
        let Some((at, close_tag)) = cut else {
            out.push_str(rest);
            break;
        };
        out.push_str(&rest[..at]);
        let tail = &rest[at..];
        match tail.to_ascii_lowercase().find(close_tag) {
            Some(i) => rest = &tail[i + close_tag.len()..],
            // An unclosed element: everything after it is inside it. Stop.
            None => break,
        }
    }

    let mut text = String::new();
    let mut in_tag = false;
    for ch in out.chars() {
        match ch {
            '<' => {
                in_tag = true;
                text.push('\n');
            }
            '>' => in_tag = false,
            c if !in_tag => text.push(c),
            _ => {}
        }
    }
    let decoded = text
        .replace("&amp;", "&")
        .replace("&lt;", "<")
        .replace("&gt;", ">")
        .replace("&quot;", "\"")
        .replace("&#39;", "'")
        .replace("&nbsp;", " ");
    let mut lines: Vec<String> = Vec::new();
    for raw in decoded.lines() {
        let line = raw.split_whitespace().collect::<Vec<_>>().join(" ");
        if line.is_empty() {
            continue;
        }
        // Collapse consecutive duplicate lines (a tag-per-line strip produces runs).
        if lines.last().map(String::as_str) == Some(line.as_str()) {
            continue;
        }
        lines.push(line);
    }
    lines.join("\n")
}

/// The `[badge]` runs a chat/prose projection paints for a literal pill, read back out of the
/// rendered text. This is the projection's OWN output, not a re-derivation from the tree.
pub fn pills_in_text(text: &str) -> Vec<String> {
    let mut found = Vec::new();
    for line in text.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with('[') && trimmed.ends_with(']') && trimmed.contains("] [") {
            found.push(trimmed.to_string());
        } else if trimmed.starts_with('[') && trimmed.ends_with(']') && !trimmed.contains(' ') {
            found.push(trimmed.to_string());
        }
    }
    found
}

/// The `<span class="pill …">word</span>` badges a web page paints.
pub fn pills_in_html(html: &str) -> Vec<String> {
    let mut found = Vec::new();
    for chunk in html.split("<span class=\"pill").skip(1) {
        let Some((attrs, rest)) = chunk.split_once('>') else {
            continue;
        };
        let Some((word, _)) = rest.split_once("</span>") else {
            continue;
        };
        let tag = attrs
            .split_once("tag-")
            .map(|(_, t)| t.trim_end_matches(['"', ' ']).to_string())
            .unwrap_or_default();
        found.push(format!("[{}] tag={tag}", visible_text(word)));
    }
    found
}
