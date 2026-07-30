//! **The deos-`ViewNode` → Telegram message text renderer.** An offering's [`Surface`] is a
//! deos affordance view-tree; a Telegram message is plain text plus an inline keyboard. This walks
//! the tree into the *text* half (room prose, party state, verified-turn count, section titles);
//! the *affordance* half (the [`deos_view::ViewNode::Menu`] rows / the passed [`Action`]s) becomes
//! the inline keyboard in [`crate::api::build_present_request`], NOT text — so the same surface
//! that paints Discord buttons paints a Telegram keyboard, no reinvention.

use deos_view::{SurfaceBackend, TelegramBackend, ViewNode};
use dreggnet_offerings::Surface;

/// Render a [`Surface`] into Telegram message text (the *non-affordance* half of the surface).
/// [`deos_view::ViewNode::Menu`]/`Button` are OMITTED — they are rendered as the inline keyboard,
/// not as text. Section titles head their blocks; text nodes are lines.
///
/// Renders through the deos-view [`TelegramBackend`] (the moved-in walker — full node coverage);
/// this crate no longer maintains its own subset walker.
///
/// ⚑ This is the PLAIN reading of the surface — the prose, as words. What the live bot puts on the
/// wire is [`render_surface_html`]; see its note for why the two exist.
pub fn render_surface_text(surface: &Surface) -> String {
    TelegramBackend.render(surface.view(), &[])
}

/// **Render a [`Surface`] for the wire** — the SAME walk as [`render_surface_text`], HTML-escaped
/// with the board fenced in `<pre>`, to be sent with
/// [`parse_mode`](crate::api::SendMessageRequest::parse_mode) set to
/// [`TELEGRAM_PARSE_MODE`](crate::api::TELEGRAM_PARSE_MODE).
///
/// ⚑ **WHY THIS IS NOT COSMETIC.** A `sendMessage` with no `parse_mode` is rendered by every
/// Telegram client in a PROPORTIONAL font. [`deos_view::coordgrid_text`] builds a board out of
/// fixed-3-character cells whose only claim to being a grid is that every cell occupies the same
/// number of characters — which is a grid in a monospace font and a ragged pile in a proportional
/// one. Every board this bot has ever sent was misaligned for that reason alone.
///
/// ⚑ **AND WHY THE ESCAPE TRAVELS WITH IT.** `parse_mode` is per-MESSAGE, not per-span: the moment
/// the board is fenced, every other line of the message — section titles, prose, identities, a
/// game's own copy — is text Telegram's HTML parser reads, and one raw `<` in any of them is a
/// `can't parse entities` refusal for the WHOLE message. So the fence and the escape are one
/// decision, made once, inside the shared walk ([`deos_view::ChatTextStyle`]) where no caller can
/// take half of it. HTML is the parse mode rather than MarkdownV2 because its escape surface is
/// three characters (`&`, `<`, `>`) instead of eighteen.
pub fn render_surface_html(surface: &Surface) -> String {
    // By module path, not the crate root: `deos_view::render_html` is the WEB backend's HTML/DOM
    // document renderer, a different renderer for a different channel.
    deos_view::telegram::render_html(surface.view())
}

/// The line the head message carries when sections were moved out. Counts them and says WHERE they
/// went, so the reader is never quietly served a truncated game.
fn continuation_note(moved: usize) -> ViewNode {
    ViewNode::Text(if moved == 1 {
        "The last part of this page did not fit in one message and is shown just above.".to_string()
    } else {
        format!(
            "The last {moved} parts of this page did not fit in one message and are shown just \
             above."
        )
    })
}

/// The children of a container that may be SPLIT, and nothing else. A `Text`, a `CoordGrid`, a
/// `Menu` — any leaf — has no seam a reader would recognise, so it is never cut.
fn splittable_children_mut(node: &mut ViewNode) -> Option<&mut Vec<ViewNode>> {
    match node {
        ViewNode::Section { children, .. }
        | ViewNode::VStack(children)
        | ViewNode::List(children)
        | ViewNode::Row(children)
        | ViewNode::Table(children) => Some(children),
        _ => None,
    }
}

/// **Detach the last splittable child, wherever the seam actually is.** Pops the trailing child of
/// the OUTERMOST container that has more than one — and recurses when a container holds exactly
/// one, because a surface whose root is a single wrapper around the real body ([`ViewNode::VStack`]
/// of one `Section`, which is how several offerings build theirs) has its seams one level down and
/// a root-only split would report "no section boundary" over a page full of them.
///
/// `false` means there is genuinely nothing left to cut on.
fn detach_last_splittable(node: &mut ViewNode, moved: &mut Vec<ViewNode>) -> bool {
    let Some(children) = splittable_children_mut(node) else {
        // A LEAF. Its only seam is inside its own prose — and a page of prose DOES have one, at a
        // line or a sentence end. Without this a surface that is one long text node under a
        // wrapper reports "no boundary" over a page full of them.
        if let ViewNode::Text(text) = node
            && let Some((keep, rest)) = split_prose_tail(text)
        {
            *text = keep;
            moved.insert(0, ViewNode::Text(rest));
            return true;
        }
        return false;
    };
    // The last child that puts TEXT in the message. A `Menu`/`Button` renders to nothing here (its
    // affordances ride the inline keyboard, not the body), so moving one would cost a companion
    // page, save no characters, and take the surface's own affordance node away from the head.
    let Some(index) = children.iter().rposition(|child| {
        !render_surface_text(&Surface(child.clone()))
            .trim()
            .is_empty()
    }) else {
        return false;
    };
    if children.len() > 1 && index > 0 {
        moved.insert(0, children.remove(index));
        return true;
    }
    // Exactly one text-bearing child: its seams are one level down. A surface whose root is a
    // single wrapper around the real body — a `VStack` of one `Section`, or the `Section("Game")`
    // the host wraps a `VStack` root in — has ALL its seams there, and a root-only split reported
    // "no section boundary" over a page full of them.
    if detach_last_splittable(&mut children[index], moved) {
        return true;
    }
    // That child is a leaf and there is something else here to keep: move the leaf whole rather
    // than reporting no seam. This is the arm that makes progress GUARANTEED, so the loop above
    // cannot stall above the ceiling while text remains to move.
    if children.len() > 1 {
        moved.insert(0, children.remove(index));
        return true;
    }
    false
}

/// The node kind, for an operator-facing refusal that has to say WHY it could not continue a
/// surface across messages. Never player copy: it names the tree, which is a fact about the build.
pub fn node_kind(node: &ViewNode) -> String {
    match node {
        ViewNode::Section {
            title, children, ..
        } => {
            format!("Section({title:?}×{})", children.len())
        }
        ViewNode::VStack(c) => format!("VStack×{}", c.len()),
        ViewNode::List(c) => format!("List×{}", c.len()),
        ViewNode::Row(c) => format!("Row×{}", c.len()),
        ViewNode::Table(c) => format!("Table×{}", c.len()),
        ViewNode::Text(t) => format!("Text[{}]", t.chars().count()),
        other => {
            let dumped = format!("{other:?}");
            let cut = dumped
                .char_indices()
                .nth(24)
                .map(|(i, _)| i)
                .unwrap_or(dumped.len());
            dumped[..cut].to_string()
        }
    }
}

/// Cut one prose node in two at the LAST seam a reader would recognise — a line break, else a
/// sentence end — keeping the first half and returning `(keep, moved)`. `None` when the text is a
/// single short run with no seam at all, which is the honest "this cannot be continued".
///
/// The cut is taken past the halfway mark so each step makes real progress; a seam in the first
/// few characters would otherwise move almost the whole node and leave a stub behind.
fn split_prose_tail(text: &str) -> Option<(String, String)> {
    let chars: Vec<char> = text.chars().collect();
    if chars.len() < 80 {
        return None;
    }
    let floor = chars.len() / 2;
    let seam = (floor..chars.len().saturating_sub(1))
        .rev()
        .find(|i| chars[*i] == '\n')
        .or_else(|| {
            (floor..chars.len().saturating_sub(2))
                .rev()
                .find(|i| matches!(chars[*i], '.' | '!' | '?' | '·') && chars[i + 1] == ' ')
        })?;
    let keep: String = chars[..=seam].iter().collect();
    let rest: String = chars[seam + 1..].iter().collect();
    let (keep, rest) = (keep.trim_end().to_string(), rest.trim_start().to_string());
    (!keep.is_empty() && !rest.is_empty()).then_some((keep, rest))
}

/// Append the continuation note to the outermost container that can hold it. Never invents a
/// container: a leaf root carries no note, and a leaf root also never splits, so the two agree.
fn note_moved(node: &mut ViewNode, moved: usize) {
    if moved == 0 {
        return;
    }
    if let Some(children) = splittable_children_mut(node) {
        children.push(continuation_note(moved));
    }
}

/// **Fit a [`Surface`] into ONE Telegram message, moving the overflow to companion pages instead of
/// refusing the whole send.**
///
/// # The hole this closes
///
/// [`crate::api::TELEGRAM_TEXT_LIMIT`] is Telegram's, it is real, and a message over it is rejected
/// by the Bot API. The adapter therefore refused an oversized interactive surface fail-closed —
/// correct as far as it went, and it meant that **an offering whose surface simply grew past 4096
/// became unplayable on Telegram outright**. Measured 2026-07-29 on the shipped catalog: the
/// dungeon rendered 4,719 characters and automatafl 4,429, so `present` returned an error, no
/// message was recorded, and every later `collect` found no presented affordance. The chat saw
/// silence; `every_offering_paints`'s ship-list assertion is what caught it.
///
/// Refusing is the right answer only when there is nothing else to do. There is: the frontend
/// already paints **non-interactive companion pages** beside a session ([`crate::TelegramFrontend::
/// present_companion_pages_result`]), which is how the proof-operation guide keeps its long
/// disclosures out of the keyboard-bearing message. This gives the surface itself the same
/// treatment — the SAME shape the keyboard already has, where a bound is enforced and what it left
/// off is named in a trailing line rather than silently dropped.
///
/// # What it does, and what it never does
///
/// Trailing children are moved out **whole**, from the end, until the head fits — so a cut always
/// falls on a seam the surface itself declared (a `Section`, a `VStack`/`List` item), never
/// mid-sentence and never inside a board. The head keeps the title, the live state and the
/// keyboard; the moved parts are returned in their original order as plain-text companion pages.
///
/// It NEVER drops anything: every moved child is in the returned pages. When there is no seam left
/// at all — a leaf root, or one unsplittable child over the ceiling — the head comes back still
/// over the ceiling and the caller refuses fail-closed, because that case genuinely cannot be sent.
///
/// ⚠ A moved child renders as PLAIN text (companion messages carry no `parse_mode`, deliberately —
/// see [`crate::TelegramFrontend::present_companion_pages_result`]), so a `CoordGrid` in a moved
/// tail would be laid out proportionally. Moving from the END keeps a board — which every shipped
/// game paints early, above its per-seat prose — in the head, and this is the reason the split is
/// tail-first rather than "drop the biggest".
pub fn fit_surface_for_wire(surface: &Surface, limit: usize) -> (Surface, Vec<String>) {
    if render_surface_html(surface).chars().count() <= limit {
        return (surface.clone(), Vec::new());
    }
    let mut body = surface.view().clone();
    let mut moved: Vec<ViewNode> = Vec::new();
    loop {
        if !detach_last_splittable(&mut body, &mut moved) {
            // No seam left. Hand back the best head there is; the caller fails closed on it.
            let mut head = body;
            note_moved(&mut head, moved.len());
            return (Surface(head), continuation_pages(&moved, limit));
        }
        let mut head = body.clone();
        note_moved(&mut head, moved.len());
        if render_surface_html(&Surface(head.clone())).chars().count() <= limit {
            return (Surface(head), continuation_pages(&moved, limit));
        }
    }
}

/// The moved children as companion pages: each rendered plain, then split on line boundaries so no
/// single page exceeds `limit` (the companion presenter validates `1..=limit` per page and would
/// otherwise refuse the whole slot). Empty renders are dropped — a blank message teaches nothing.
fn continuation_pages(moved: &[ViewNode], limit: usize) -> Vec<String> {
    let mut pages = Vec::new();
    for node in moved {
        let text = render_surface_text(&Surface(node.clone()));
        for chunk in chunk_by_lines(text.trim(), limit) {
            pages.push(chunk);
        }
    }
    pages
}

/// Break `text` into pieces of at most `limit` CHARACTERS, cutting on newlines wherever possible.
/// A single line longer than `limit` is cut at `limit` characters (never at a byte boundary that
/// could split a `char`), because the alternative is a page the Bot API refuses.
fn chunk_by_lines(text: &str, limit: usize) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    if text.is_empty() {
        return out;
    }
    let mut current = String::new();
    for line in text.lines() {
        let line_len = line.chars().count();
        let extra = if current.is_empty() { 0 } else { 1 };
        if !current.is_empty() && current.chars().count() + extra + line_len > limit {
            out.push(std::mem::take(&mut current));
        }
        if line_len > limit {
            // One over-long line: emit it in `limit`-character pieces, on char boundaries.
            if !current.is_empty() {
                out.push(std::mem::take(&mut current));
            }
            let mut piece = String::new();
            for c in line.chars() {
                if piece.chars().count() == limit {
                    out.push(std::mem::take(&mut piece));
                }
                piece.push(c);
            }
            if !piece.is_empty() {
                out.push(piece);
            }
            continue;
        }
        if !current.is_empty() {
            current.push('\n');
        }
        current.push_str(line);
    }
    if !current.is_empty() {
        out.push(current);
    }
    out
}
