//! The terminal VIEW: a gpui entity that renders the [`Terminal`] grid as
//! monospace rows, owns a `FocusHandle`, turns key events into PTY bytes, and
//! drives a steady repaint so shell output streams in live.
//!
//! Lean by design — no custom GPU paint element. Each visible grid row is laid
//! out as a flex line of style-runs (contiguous same-color/-weight cells merged
//! into one styled span). The grid is sized to the rendered viewport: on each
//! frame we measure the monospace cell box and resize the PTY to fit.

use std::time::Duration;

use gpui::{
    div, px, rgb, Bounds, Context, FocusHandle, Focusable, InteractiveElement, IntoElement,
    KeyDownEvent, ParentElement, Pixels, Render, ScrollWheelEvent, SharedString, Styled, Window,
};

use crate::keymap::to_esc_str;
use crate::model::{RenderCell, Rgba, Terminal, TermSize, DEFAULT_BG, DEFAULT_FG};
use crate::transport::TerminalTransport;

/// Font size (px) and line-height multiple for the terminal grid.
const FONT_SIZE: f32 = 13.0;
const LINE_HEIGHT_MUL: f32 = 1.25;
const FONT_FAMILY: &str = "Menlo";

/// A gpui terminal view over a live [`Terminal`].
pub struct TerminalView {
    pub terminal: Terminal,
    focus: FocusHandle,
    /// Last grid generation we painted; used to avoid redundant snapshots.
    last_generation: u64,
    /// Pixel size of one character cell, measured from the text system. `None`
    /// until the first frame measures it.
    cell_size: Option<(Pixels, Pixels)>,
    /// Last viewport bounds we sized the PTY to.
    last_bounds: Option<Bounds<Pixels>>,
    option_as_meta: bool,
}

impl TerminalView {
    /// Build a view over an already-spawned terminal, and start the repaint loop.
    pub fn new(terminal: Terminal, cx: &mut Context<Self>) -> Self {
        let focus = cx.focus_handle();

        // Steady repaint loop driven by the gpui foreground executor: each tick
        // re-enters the entity and, if the model's grid generation advanced (the
        // IO thread parsed new shell output), fires `cx.notify()` so the next
        // frame re-snapshots and paints. ~30fps keeps streamed output smooth.
        // (The IO thread can't poke gpui directly — gpui's `AsyncApp` is
        // !Send/!Sync — so the timer is the wake path, not a cross-thread waker.)
        cx.spawn(async move |this, cx| loop {
            cx.background_executor()
                .timer(Duration::from_millis(33))
                .await;
            if this
                .update(cx, |this, cx| {
                    if this.terminal.generation() != this.last_generation {
                        cx.notify();
                    }
                })
                .is_err()
            {
                break;
            }
        })
        .detach();

        Self {
            terminal,
            focus,
            last_generation: u64::MAX,
            cell_size: None,
            last_bounds: None,
            option_as_meta: false,
        }
    }

    /// Convenience: spawn `$SHELL` and wrap it in a view entity.
    pub fn spawn_shell(cx: &mut Context<Self>) -> anyhow::Result<Self> {
        let terminal = Terminal::spawn(
            None,
            std::env::current_dir().ok(),
            std::env::vars().collect(),
            TermSize::new(80, 24),
        )?;
        Ok(Self::new(terminal, cx))
    }

    fn on_key_down(&mut self, ev: &KeyDownEvent, cx: &mut Context<Self>) {
        let content = self.terminal.content();
        let modes = content.key_modes();

        // Keystrokes leave through the transport SEAM (`TerminalTransport::write`)
        // — the same trait the wasm `WsTransport` implements. On native it lands
        // in the local PTY; on web the identical call rides the WebSocket.
        if let Some(esc) = to_esc_str(&ev.keystroke, modes, self.option_as_meta) {
            TerminalTransport::write(&self.terminal, esc.as_bytes());
            cx.notify();
            return;
        }

        // No escape sequence: send the typed character(s) verbatim.
        if let Some(text) = &ev.keystroke.key_char {
            if !text.is_empty() {
                TerminalTransport::write(&self.terminal, text.as_bytes());
                cx.notify();
                return;
            }
        }

        // Fall back to a single printable key with no modifiers (e.g. when the
        // platform didn't populate key_char).
        let key = &ev.keystroke.key;
        let m = &ev.keystroke.modifiers;
        if !m.control && !m.platform && !m.function && key.chars().count() == 1 {
            TerminalTransport::write(&self.terminal, key.as_bytes());
            cx.notify();
        }
    }

    fn on_scroll(&mut self, ev: &ScrollWheelEvent, _window: &mut Window, cx: &mut Context<Self>) {
        let (_, cell_h) = self.cell_size.unwrap_or((px(8.), px(16.)));
        let dy = ev.delta.pixel_delta(cell_h).y;
        let lines = (f32::from(dy) / f32::from(cell_h)).round() as i32;
        if lines != 0 {
            self.terminal.scroll(lines);
            cx.notify();
        }
    }

    /// Measure the cell box and resize the PTY to the viewport, if it changed.
    fn sync_size(&mut self, bounds: Bounds<Pixels>, window: &mut Window, cx: &mut Context<Self>) {
        let rem = window.rem_size();
        let font_size = px(FONT_SIZE);
        let font = gpui::Font {
            family: FONT_FAMILY.into(),
            features: Default::default(),
            fallbacks: None,
            weight: Default::default(),
            style: Default::default(),
        };
        let cell_w = cx
            .text_system()
            .resolve_font(&font)
            .pipe(|font_id| cx.text_system().advance(font_id, font_size, 'm').ok())
            .map(|adv| adv.width)
            .unwrap_or(px(FONT_SIZE * 0.6));
        let cell_h = px(FONT_SIZE * LINE_HEIGHT_MUL);
        let _ = rem;
        self.cell_size = Some((cell_w, cell_h));

        let cols = (f32::from(bounds.size.width) / f32::from(cell_w)).floor() as usize;
        let lines = (f32::from(bounds.size.height) / f32::from(cell_h)).floor() as usize;
        let size = TermSize::new(cols.max(2), lines.max(1));

        let changed = self
            .last_bounds
            .map(|b| b.size != bounds.size)
            .unwrap_or(true);
        if changed {
            self.last_bounds = Some(bounds);
            // The inherent, cell-metric-aware resize (disambiguated from the
            // `TerminalTransport::resize` seam method, which is in scope here).
            Terminal::resize(
                &mut self.terminal,
                size,
                f32::from(cell_w) as u16,
                f32::from(cell_h) as u16,
            );
        }
    }
}

// A tiny `.pipe()` so the font resolution above reads as a chain.
trait Pipe: Sized {
    fn pipe<R>(self, f: impl FnOnce(Self) -> R) -> R {
        f(self)
    }
}
impl<T> Pipe for T {}

fn rgba_to_rgb(c: Rgba) -> gpui::Rgba {
    rgb(((c.r as u32) << 16) | ((c.g as u32) << 8) | (c.b as u32)).into()
}

impl Focusable for TerminalView {
    fn focus_handle(&self, _cx: &gpui::App) -> FocusHandle {
        self.focus.clone()
    }
}

impl Render for TerminalView {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        let content = self.terminal.content();
        self.last_generation = self.terminal.generation();

        let (cell_w, cell_h) = self.cell_size.unwrap_or((px(8.), px(16.)));

        // Bucket cells by row. The grid lines run -history..screen_lines; we only
        // paint the visible viewport rows 0..screen_lines (display_iter already
        // yields the viewport after display_offset).
        let cols = content.columns.max(1);
        let rows = content.screen_lines.max(1);
        let mut grid: Vec<Vec<Option<RenderCell>>> = vec![vec![None; cols]; rows];
        // display_iter lines are absolute grid lines; the topmost visible line is
        // `-display_offset`. Map line -> row index 0..rows.
        for cell in &content.cells {
            let row = cell.line + content.display_offset as i32;
            if row >= 0 && (row as usize) < rows && cell.column < cols {
                grid[row as usize][cell.column] = Some(cell.clone());
            }
        }

        let cursor_row = content.cursor_line + content.display_offset as i32;

        let mut row_elems = Vec::with_capacity(rows);
        for (r, row_cells) in grid.iter().enumerate() {
            let mut spans: Vec<gpui::AnyElement> = Vec::new();
            let mut col = 0usize;
            while col < cols {
                // Merge a run of cells sharing fg/weight/italic into one span.
                let here = &row_cells[col];
                let (text_run, fg, bold, italic, underline) = collect_run(row_cells, &mut col);
                let is_blank_run = text_run.chars().all(|c| c == ' ');
                let _ = here;
                if is_blank_run {
                    // Blank: just reserve width with an empty sized div.
                    spans.push(
                        div()
                            .w(cell_w * text_run.chars().count() as f32)
                            .h(cell_h)
                            .into_any_element(),
                    );
                } else {
                    let mut span = div()
                        .h(cell_h)
                        .text_color(rgba_to_rgb(fg))
                        .child(SharedString::from(text_run));
                    if bold {
                        span = span.font_weight(gpui::FontWeight::BOLD);
                    }
                    if italic {
                        span = span.italic();
                    }
                    if underline {
                        span = span.underline();
                    }
                    spans.push(span.into_any_element());
                }
            }

            let mut row_div = div().flex().flex_row().h(cell_h).children(spans);

            // Draw the cursor as a filled block behind its cell on this row.
            if content.cursor_visible && cursor_row == r as i32 && content.cursor_column < cols {
                row_div = row_div.relative().child(
                    div()
                        .absolute()
                        .left(cell_w * content.cursor_column as f32)
                        .top(px(0.))
                        .w(cell_w)
                        .h(cell_h)
                        .bg(rgba_to_rgb(DEFAULT_FG))
                        .opacity(0.55),
                );
            }
            row_elems.push(row_div);
        }

        div()
            .id("deos-terminal")
            .track_focus(&self.focus)
            .key_context("Terminal")
            .on_key_down(cx.listener(|this, ev: &KeyDownEvent, _w, cx| this.on_key_down(ev, cx)))
            .on_scroll_wheel(cx.listener(|this, ev: &ScrollWheelEvent, w, cx| {
                this.on_scroll(ev, w, cx)
            }))
            .size_full()
            .overflow_hidden()
            .bg(rgba_to_rgb(DEFAULT_BG))
            .text_color(rgba_to_rgb(DEFAULT_FG))
            .font_family(FONT_FAMILY)
            .text_size(px(FONT_SIZE))
            .child(
                // A canvas to measure the body and keep the PTY grid sized to it.
                gpui::canvas(
                    {
                        let view = cx.entity();
                        move |bounds, window, cx| {
                            view.update(cx, |this, cx| this.sync_size(bounds, window, cx));
                            bounds
                        }
                    },
                    |_bounds, _measured, _window, _cx| {},
                )
                .absolute()
                .size_full(),
            )
            .child(div().flex().flex_col().children(row_elems))
    }
}

/// Collect a maximal run of cells from `col` onward that share the same visual
/// style, returning the run's text and that shared style. Advances `col`.
fn collect_run(
    row: &[Option<RenderCell>],
    col: &mut usize,
) -> (String, Rgba, bool, bool, bool) {
    let start = *col;
    let style_of = |c: &Option<RenderCell>| -> (Rgba, bool, bool, bool) {
        match c {
            Some(cell) => (cell.fg, cell.bold, cell.italic, cell.underline),
            None => (DEFAULT_FG, false, false, false),
        }
    };
    let (fg, bold, italic, underline) = style_of(&row[start]);
    let mut text = String::new();
    while *col < row.len() {
        let (f, b, i, u) = style_of(&row[*col]);
        if f != fg || b != bold || i != italic || u != underline {
            break;
        }
        let ch = match &row[*col] {
            Some(cell) => cell.c,
            None => ' ',
        };
        text.push(if ch == '\0' { ' ' } else { ch });
        *col += 1;
    }
    (text, fg, bold, italic, underline)
}
