//! The document VIEWER — render a document's STRUCTURE, not its flat bytes.
//!
//! Where [`crate::editor::Editor`] is the *authoring* face of a
//! [`dregg_doc::RopeDoc`] (type into a buffer, each save accrues a patch), this is
//! the *inspecting* face: it renders the document's **provenance** and its
//! **conflicts** as first-class UI.
//!
//! Two panes, both read off the durable patch history (never the buffer bytes):
//!
//! * **Blame / timeline** — every live span in document order, attributed to the
//!   author who wrote it and the patch that introduced it. Correct by
//!   construction: the attribution rides the content-addressed atom, so it does
//!   NOT smear when surrounding text moves (the git-blame middle-insert failure
//!   cannot occur). Each author gets a stable swatch colour.
//!
//! * **Conflict objects** — the keystone. A genuine concurrent clash (two pens at
//!   one tail) is shown as BOTH alternatives side by side, each labelled with its
//!   author — an inspectable object, NEVER a `<<<<<<<` text wound. A field clash
//!   (the non-monotone boundary) is shown the same way, tagged with the field.
//!
//! The viewer holds a SNAPSHOT (`Vec<BlameLine>` + `Rendered`) so it renders
//! without borrowing a live `RopeDoc` across gpui frames; [`DocViewer::set_doc`] /
//! [`DocViewer::refresh_from`] re-snapshot from a document (e.g. after a save or a
//! merge). It is `Render`-shaped, so it drops into a dock tab or a window pane.

use dregg_doc::{BlameLine, ConflictRegion, Regime, RopeDoc, Segment};
use gpui::{
    div, px, App, Context, FocusHandle, Focusable, Hsla, InteractiveElement as _, IntoElement,
    ParentElement as _, Render, SharedString, Styled as _, Window,
};
use gpui_component::{h_flex, v_flex, ActiveTheme as _, StyledExt as _};

/// A read-only view over a document's provenance + conflicts. Holds a snapshot of
/// the blame lines and the rendered structure (clean runs + conflict objects), so
/// it can render across frames without borrowing a live document.
pub struct DocViewer {
    /// Per-atom blame in document order (who/which-patch wrote each live span).
    blame: Vec<BlameLine>,
    /// The rendered structure: clean runs interleaved with first-class conflict
    /// regions. The conflict regions are what this viewer exists to surface.
    segments: Vec<Segment>,
    /// A short title (the document name / source).
    title: SharedString,
    /// How many patches the document's history holds.
    patch_count: usize,
    focus: FocusHandle,
}

impl DocViewer {
    /// An empty viewer (nothing open yet).
    pub fn new(cx: &mut App) -> Self {
        Self {
            blame: Vec::new(),
            segments: Vec::new(),
            title: SharedString::from("no document"),
            patch_count: 0,
            focus: cx.focus_handle(),
        }
    }

    /// Snapshot a document into the viewer: read its blame + rendered structure.
    /// Call after a save / merge to refresh what's shown.
    pub fn refresh_from(&mut self, doc: &RopeDoc, title: impl Into<SharedString>) {
        self.blame = doc.blame();
        self.segments = doc.rendered().segments;
        self.title = title.into();
        self.patch_count = doc.history().len();
    }

    /// Build a viewer already populated from a document.
    pub fn from_doc(doc: &RopeDoc, title: impl Into<SharedString>, cx: &mut App) -> Self {
        let mut v = Self::new(cx);
        v.refresh_from(doc, title);
        v
    }

    /// Whether the snapshot currently carries a conflict object.
    pub fn has_conflict(&self) -> bool {
        self.segments
            .iter()
            .any(|s| matches!(s, Segment::Conflict(_)))
    }
}

/// A stable, legible swatch colour for an author id — so the same author reads as
/// the same colour across the blame gutter and the conflict alternatives.
fn author_color(author: u64, cx: &App) -> Hsla {
    let t = cx.theme();
    // A small fixed palette cycled by author id; deterministic so a co-author's
    // colour is consistent everywhere in the view.
    let palette = [
        t.blue,
        t.green,
        t.magenta,
        t.yellow,
        t.red,
        t.cyan,
        t.blue_light,
        t.green_light,
    ];
    palette[(author as usize) % palette.len()]
}

impl DocViewer {
    /// One blame row: a coloured author swatch + author/patch labels + the span.
    fn blame_row(&self, line: &BlameLine, cx: &App) -> impl IntoElement {
        let color = author_color(line.author.0, cx);
        // Show the span on one visual line (collapse the trailing newline).
        let text = line.content.trim_end_matches('\n').to_string();
        let text = if text.is_empty() {
            SharedString::from("⏎")
        } else {
            SharedString::from(text)
        };
        h_flex()
            .w_full()
            .gap_2()
            .px_2()
            .py_0p5()
            .items_center()
            // The author swatch — the colour key.
            .child(div().w(px(8.)).h(px(14.)).rounded_sm().bg(color))
            .child(
                div()
                    .w(px(64.))
                    .text_xs()
                    .text_color(cx.theme().muted_foreground)
                    .child(SharedString::from(format!("@{}", line.author.0))),
            )
            .child(
                div()
                    .flex_1()
                    .text_sm()
                    .text_color(cx.theme().foreground)
                    .font_family("monospace")
                    .child(text),
            )
    }

    /// One conflict object: BOTH alternatives shown side by side, each labelled
    /// with its author — the two-pens-at-one-tail rendered as an inspectable
    /// object, not a `<<<<<<<` wound. A field clash is tagged with the field name.
    fn conflict_card(&self, region: &ConflictRegion, cx: &App) -> impl IntoElement {
        let (label, accent) = match region.regime {
            // A prose antichain: illusory / unilaterally resolvable — a softer
            // warning tone.
            Regime::Prose => ("concurrent edit", cx.theme().warning),
            // A field/conservation clash: a REAL conflict that may need consensus.
            Regime::Field => ("field clash", cx.theme().danger),
        };
        let header = match &region.field {
            Some(f) => format!("⚡ {label} · field “{f}” — both alternatives live"),
            None => format!("⚡ {label} — both alternatives live, no order chosen"),
        };

        let mut card = v_flex()
            .w_full()
            .gap_1()
            .p_2()
            .my_1()
            .rounded_md()
            .border_1()
            .border_color(accent)
            .bg(cx.theme().secondary)
            .child(
                div()
                    .text_xs()
                    .font_semibold()
                    .text_color(accent)
                    .child(SharedString::from(header)),
            );

        // Each alternative as its own labelled, author-coloured block.
        for alt in &region.alternatives {
            let color = author_color(alt.provenance.author.0, cx);
            let body = alt.text.trim_end_matches('\n').to_string();
            card = card.child(
                h_flex()
                    .w_full()
                    .gap_2()
                    .items_start()
                    .child(div().w(px(4.)).h_full().min_h(px(18.)).rounded_sm().bg(color))
                    .child(
                        v_flex()
                            .flex_1()
                            .gap_0p5()
                            .child(
                                div()
                                    .text_xs()
                                    .text_color(cx.theme().muted_foreground)
                                    .child(SharedString::from(format!(
                                        "@{} · patch {:#x}",
                                        alt.provenance.author.0,
                                        // Short patch fingerprint.
                                        (alt.provenance.patch.0 as u64)
                                    ))),
                            )
                            .child(
                                div()
                                    .text_sm()
                                    .font_family("monospace")
                                    .text_color(cx.theme().foreground)
                                    .child(SharedString::from(if body.is_empty() {
                                        "(empty)".to_string()
                                    } else {
                                        body
                                    })),
                            ),
                    ),
            );
        }
        card
    }
}

impl Focusable for DocViewer {
    fn focus_handle(&self, _: &App) -> FocusHandle {
        self.focus.clone()
    }
}

impl Render for DocViewer {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        let theme = cx.theme();

        // Header: title + patch count + conflict indicator.
        let conflict_badge = if self.has_conflict() {
            div()
                .px_2()
                .py_0p5()
                .rounded_sm()
                .bg(theme.warning)
                .text_xs()
                .text_color(theme.warning_foreground)
                .child("⚡ conflicts")
        } else {
            div()
                .px_2()
                .py_0p5()
                .rounded_sm()
                .bg(theme.success)
                .text_xs()
                .text_color(theme.success_foreground)
                .child("✓ clean")
        };

        let header = h_flex()
            .w_full()
            .px_2()
            .py_1()
            .gap_2()
            .items_center()
            .bg(theme.secondary)
            .border_b_1()
            .border_color(theme.border)
            .child(
                div()
                    .font_semibold()
                    .text_sm()
                    .text_color(theme.foreground)
                    .child(self.title.clone()),
            )
            .child(
                div()
                    .text_xs()
                    .text_color(theme.muted_foreground)
                    .child(SharedString::from(format!("{} patches", self.patch_count))),
            )
            .child(div().flex_1())
            .child(conflict_badge);

        // The structure pane: clean runs as blame-coloured rows, conflict regions
        // as inspectable cards, in document order.
        let mut body = v_flex().w_full().gap_0().p_1();
        // Index into the blame list as we emit clean runs (blame is per live atom
        // in the same document order; a clean run renders its atoms' blame rows).
        let mut blame_iter = self.blame.iter().peekable();
        for seg in &self.segments {
            match seg {
                Segment::Clean(text) => {
                    // Emit one blame row per atom whose content the clean run
                    // covers, consuming from the blame list in order. The clean
                    // run's text is the concatenation of those atoms; we match by
                    // walking blame entries until we've covered the run's bytes.
                    let mut covered = String::new();
                    while covered.len() < text.len() {
                        let Some(line) = blame_iter.next() else { break };
                        covered.push_str(&line.content);
                        body = body.child(self.blame_row(line, cx));
                    }
                }
                Segment::Conflict(region) => {
                    body = body.child(self.conflict_card(region, cx));
                }
            }
        }
        // Any trailing blame (e.g. atoms inside an unwalked region) — show them so
        // nothing is silently dropped from the provenance view.
        for line in blame_iter {
            body = body.child(self.blame_row(line, cx));
        }

        v_flex()
            .size_full()
            .bg(theme.background)
            .track_focus(&self.focus)
            .child(header)
            .child(div().flex_1().min_h(px(0.)).overflow_hidden().child(body))
    }
}
