//! The terminal MODEL: a real PTY over `$SHELL`, the alacritty event-loop IO
//! thread parsing its byte stream into a `Term` grid, and a content snapshot
//! the view paints.
//!
//! This is the lean equivalent of Zed's `terminal/src/alacritty.rs` +
//! `terminal.rs`, stripped to the substance: open a PTY, spawn the event loop,
//! write input bytes, resize, read renderable content. No settings/theme/task/
//! project coupling.

use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;

use alacritty_terminal::event::{Event as AlacEvent, EventListener, Notify, WindowSize};
use alacritty_terminal::event_loop::{EventLoop, Msg, Notifier};
use alacritty_terminal::grid::Dimensions;
use alacritty_terminal::sync::FairMutex;
use alacritty_terminal::term::cell::Flags;
use alacritty_terminal::term::{Config, Term, TermMode};
use alacritty_terminal::tty::{self, Options as PtyOptions, Shell as PtyShell};
use alacritty_terminal::vte::ansi::{Color, CursorShape as AlacCursorShape, NamedColor, Rgb};

use crate::keymap::Modes;

/// Default starting grid size (columns × lines). The view resizes the PTY to the
/// real cell grid as soon as it has a measured layout.
pub const DEFAULT_COLS: u16 = 80;
pub const DEFAULT_LINES: u16 = 24;

/// A single rendered cell: a character plus resolved RGB colors and a few flags.
#[derive(Clone, Debug)]
pub struct RenderCell {
    pub c: char,
    pub line: i32,
    pub column: usize,
    pub fg: Rgba,
    pub bg: Rgba,
    pub bold: bool,
    pub italic: bool,
    pub underline: bool,
    pub inverse: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Rgba {
    pub r: u8,
    pub g: u8,
    pub b: u8,
}

impl Rgba {
    pub const fn new(r: u8, g: u8, b: u8) -> Self {
        Self { r, g, b }
    }
}

/// A snapshot of the terminal's visible content, taken under the grid lock and
/// handed to the view to paint. Self-contained (owns its cells), so the view
/// never holds the grid lock while rendering.
#[derive(Clone, Debug)]
pub struct TerminalContent {
    pub cells: Vec<RenderCell>,
    pub columns: usize,
    pub screen_lines: usize,
    /// Cursor grid point (line is viewport-relative after display-offset adjust).
    pub cursor_line: i32,
    pub cursor_column: usize,
    pub cursor_visible: bool,
    pub display_offset: usize,
    /// Whether the terminal is in DECCKM application-cursor mode (for key encoding).
    pub app_cursor: bool,
}

impl TerminalContent {
    pub fn key_modes(&self) -> Modes {
        if self.app_cursor {
            Modes::APP_CURSOR
        } else {
            Modes::NONE
        }
    }
}

/// Event listener the alacritty event loop calls (on the IO thread). We keep it
/// minimal: track child-exit, and flag a "wakeup" generation the view polls so
/// it knows the grid changed and a repaint is due. An optional waker callback
/// lets a host (e.g. the gpui view) request an immediate repaint.
#[derive(Clone)]
pub struct DeosListener {
    inner: Arc<ListenerState>,
}

struct ListenerState {
    generation: AtomicU64,
    exited: AtomicBool,
    title: parking_lot::Mutex<Option<String>>,
    waker: parking_lot::Mutex<Option<Box<dyn Fn() + Send + Sync>>>,
}

impl DeosListener {
    fn new() -> Self {
        Self {
            inner: Arc::new(ListenerState {
                generation: AtomicU64::new(0),
                exited: AtomicBool::new(false),
                title: parking_lot::Mutex::new(None),
                waker: parking_lot::Mutex::new(None),
            }),
        }
    }

    pub fn generation(&self) -> u64 {
        self.inner.generation.load(Ordering::Relaxed)
    }

    pub fn has_exited(&self) -> bool {
        self.inner.exited.load(Ordering::Relaxed)
    }

    pub fn title(&self) -> Option<String> {
        self.inner.title.lock().clone()
    }

    /// Install a callback fired whenever the grid changes (Wakeup/exit/bell), so
    /// the host can schedule a repaint promptly rather than only on its timer.
    pub fn set_waker<F: Fn() + Send + Sync + 'static>(&self, f: F) {
        *self.inner.waker.lock() = Some(Box::new(f));
    }

    fn bump(&self) {
        self.inner.generation.fetch_add(1, Ordering::Relaxed);
        if let Some(waker) = self.inner.waker.lock().as_ref() {
            waker();
        }
    }
}

impl EventListener for DeosListener {
    fn send_event(&self, event: AlacEvent) {
        match event {
            AlacEvent::Wakeup => self.bump(),
            AlacEvent::Bell => self.bump(),
            AlacEvent::Title(t) => {
                *self.inner.title.lock() = Some(t);
                self.bump();
            }
            AlacEvent::ResetTitle => {
                *self.inner.title.lock() = None;
                self.bump();
            }
            AlacEvent::Exit | AlacEvent::ChildExit(_) => {
                self.inner.exited.store(true, Ordering::Relaxed);
                self.bump();
            }
            // PtyWrite (terminal-originated writes, e.g. DA responses) and the
            // clipboard/color/cursor events aren't wired in this lean model; the
            // common interactive path (shell I/O) doesn't need them.
            _ => {}
        }
    }
}

/// Size descriptor implementing alacritty's `Dimensions`, used to size the
/// `Term` grid and resize the PTY.
#[derive(Clone, Copy, Debug)]
pub struct TermSize {
    pub columns: usize,
    pub screen_lines: usize,
}

impl TermSize {
    pub fn new(columns: usize, screen_lines: usize) -> Self {
        Self {
            columns: columns.max(2),
            screen_lines: screen_lines.max(1),
        }
    }
}

impl Dimensions for TermSize {
    fn total_lines(&self) -> usize {
        self.screen_lines
    }
    fn screen_lines(&self) -> usize {
        self.screen_lines
    }
    fn columns(&self) -> usize {
        self.columns
    }
}

fn window_size(size: TermSize, cell_w: u16, cell_h: u16) -> WindowSize {
    WindowSize {
        num_lines: size.screen_lines as u16,
        num_cols: size.columns as u16,
        cell_width: cell_w,
        cell_height: cell_h,
    }
}

/// A live terminal: the shared `Term` grid, the PTY notifier (input + resize),
/// and the listener state. Dropping it shuts the event loop down.
pub struct Terminal {
    term: Arc<FairMutex<Term<DeosListener>>>,
    /// The PTY notifier (input + resize). `None` for a SEEDED terminal — a grid
    /// driven by recorded bytes with no live child process (used by the headless
    /// showcase bake: a deterministic recorded shell session, no `$SHELL` race).
    notifier: Option<Notifier>,
    listener: DeosListener,
    size: TermSize,
    cell_w: u16,
    cell_h: u16,
}

impl Terminal {
    /// Spawn `$SHELL` (or `shell_override`) on a fresh PTY and start the event
    /// loop. `working_directory` is the shell's cwd; `env` are extra vars.
    pub fn spawn(
        shell_override: Option<(String, Vec<String>)>,
        working_directory: Option<std::path::PathBuf>,
        env: HashMap<String, String>,
        size: TermSize,
    ) -> anyhow::Result<Self> {
        let listener = DeosListener::new();

        let config = Config {
            scrolling_history: 10_000,
            ..Config::default()
        };

        let term = Term::new(config, &size, listener.clone());
        let term = Arc::new(FairMutex::new(term));

        let shell = shell_override.map(|(program, args)| PtyShell::new(program, args));

        let options = PtyOptions {
            shell,
            working_directory,
            drain_on_exit: true,
            env,
            #[cfg(not(windows))]
            child_signal_mask: None,
            #[cfg(target_os = "windows")]
            escape_args: true,
        };

        // Reasonable default cell metrics; the view corrects them on first layout.
        let cell_w = 8u16;
        let cell_h = 16u16;

        let pty = tty::new(&options, window_size(size, cell_w, cell_h), 0)
            .map_err(|e| anyhow::anyhow!("failed to open pty: {e}"))?;

        let event_loop = EventLoop::new(
            term.clone(),
            listener.clone(),
            pty,
            options.drain_on_exit,
            false,
        )
        .map_err(|e| anyhow::anyhow!("failed to create terminal event loop: {e}"))?;

        let channel = event_loop.channel();
        let _io_thread = event_loop.spawn();
        let notifier = Notifier(channel);

        Ok(Self {
            term,
            notifier: Some(notifier),
            listener,
            size,
            cell_w,
            cell_h,
        })
    }

    /// Build a SEEDED terminal: an alacritty `Term` grid driven by a recorded
    /// byte stream (a captured shell session) through the VTE parser, with NO
    /// PTY and no child process. The grid is fully populated and static — exactly
    /// what a deterministic headless render (the showcase bake) wants: a real
    /// terminal grid showing a real-looking `cargo`/`git` session without racing
    /// a live `$SHELL`. `bytes` is fed verbatim (include `\r\n`, ANSI SGR, etc.).
    pub fn seeded(size: TermSize, bytes: &[u8]) -> Self {
        use alacritty_terminal::vte::ansi::Processor;

        let listener = DeosListener::new();
        let config = Config {
            scrolling_history: 10_000,
            ..Config::default()
        };
        let term = Term::new(config, &size, listener.clone());
        let term = Arc::new(FairMutex::new(term));

        // Drive the recorded bytes straight through the ANSI processor into the
        // grid — the same parse the IO thread would do for live PTY output, but
        // synchronous and with no child.
        {
            let mut guard = term.lock();
            let mut processor: Processor = Processor::new();
            for &b in bytes {
                processor.advance(&mut *guard, &[b]);
            }
        }
        listener.bump();

        Self {
            term,
            notifier: None,
            listener,
            size,
            cell_w: 8,
            cell_h: 16,
        }
    }

    /// A clone of the listener so a host can install a waker / read generation.
    pub fn listener(&self) -> DeosListener {
        self.listener.clone()
    }

    pub fn has_exited(&self) -> bool {
        self.listener.has_exited()
    }

    pub fn title(&self) -> Option<String> {
        self.listener.title()
    }

    /// Generation counter — increments on every grid change; the view diffs it.
    pub fn generation(&self) -> u64 {
        self.listener.generation()
    }

    /// Write raw bytes to the PTY (input the shell reads on its stdin).
    pub fn write(&self, bytes: impl Into<std::borrow::Cow<'static, [u8]>>) {
        // A seeded terminal has no PTY to write to — input is a no-op.
        if let Some(notifier) = &self.notifier {
            notifier.notify(bytes);
        }
    }

    /// Write a UTF-8 string to the PTY.
    pub fn write_str(&self, s: &str) {
        self.write(s.as_bytes().to_vec());
    }

    /// Scroll the display by `lines` (positive = toward history).
    pub fn scroll(&self, lines: i32) {
        use alacritty_terminal::grid::Scroll;
        let mut term = self.term.lock();
        term.scroll_display(Scroll::Delta(lines));
        // Scrolling changes what's visible; nudge the generation so the view
        // repaints even though no PTY byte arrived.
        self.listener.bump();
    }

    /// Resize the grid + PTY to a new column/line count and cell pixel metrics.
    pub fn resize(&mut self, size: TermSize, cell_w: u16, cell_h: u16) {
        if size.columns == self.size.columns
            && size.screen_lines == self.size.screen_lines
            && cell_w == self.cell_w
            && cell_h == self.cell_h
        {
            return;
        }
        self.size = size;
        self.cell_w = cell_w.max(1);
        self.cell_h = cell_h.max(1);
        self.term.lock().resize(size);
        // `Notifier` isn't `Clone`, but its inner `EventLoopSender` is; resize is
        // just a `Msg::Resize` down that channel. A seeded terminal has no PTY to
        // resize — the grid resize above is the whole story.
        if let Some(notifier) = &self.notifier {
            let _ = notifier
                .0
                .send(Msg::Resize(window_size(size, self.cell_w, self.cell_h)));
        }
    }

    pub fn size(&self) -> TermSize {
        self.size
    }

    /// Take a self-contained snapshot of the visible grid for the view to paint.
    pub fn content(&self) -> TerminalContent {
        let term = self.term.lock();
        let renderable = term.renderable_content();
        let colors = renderable.colors;

        let mut cells = Vec::new();
        for indexed in renderable.display_iter {
            let cell = indexed.cell;
            // Skip the trailing spacer half of a wide character.
            if cell.flags.contains(Flags::WIDE_CHAR_SPACER) {
                continue;
            }
            let mut fg = resolve_color(cell.fg, colors, /*is_fg*/ true);
            let mut bg = resolve_color(cell.bg, colors, /*is_fg*/ false);
            let inverse = cell.flags.contains(Flags::INVERSE);
            if inverse {
                std::mem::swap(&mut fg, &mut bg);
            }
            // Don't bother emitting empty default-bg blanks (the view fills the
            // background); keeps the cell vec small for fast frames.
            if cell.c == ' '
                && !inverse
                && bg == DEFAULT_BG
                && cell.flags.is_empty()
            {
                continue;
            }
            cells.push(RenderCell {
                c: cell.c,
                line: indexed.point.line.0,
                column: indexed.point.column.0,
                fg,
                bg,
                bold: cell.flags.contains(Flags::BOLD),
                italic: cell.flags.contains(Flags::ITALIC),
                underline: cell.flags.intersects(Flags::ALL_UNDERLINES),
                inverse,
            });
        }

        let cursor = renderable.cursor;
        let cursor_visible = cursor.shape != AlacCursorShape::Hidden;
        let mode = renderable.mode;

        TerminalContent {
            cells,
            columns: term.columns(),
            screen_lines: term.screen_lines(),
            cursor_line: cursor.point.line.0,
            cursor_column: cursor.point.column.0,
            cursor_visible,
            display_offset: renderable.display_offset,
            app_cursor: mode.contains(TermMode::APP_CURSOR),
        }
    }
}

impl Drop for Terminal {
    fn drop(&mut self) {
        if let Some(notifier) = &self.notifier {
            let _ = notifier.0.send(Msg::Shutdown);
        }
    }
}

/// The native local PTY behind the transport seam: the view writes keystrokes
/// through this trait, the same one the wasm `WsTransport` implements. The grid
/// (the alacritty `Term`) is the output sink the view snapshots via
/// [`Terminal::content`]; the real resize (cell-metric-aware, `&mut`) is
/// [`Terminal::resize`], which the trait's `&self` `resize` mirrors best-effort.
impl crate::transport::TerminalTransport for Terminal {
    fn write(&self, bytes: &[u8]) {
        self.write(bytes.to_vec());
    }

    fn resize(&self, cols: u16, rows: u16) {
        // Resize the grid (the lock path needs only `&self`); the PTY winsize is
        // updated by the view's `&mut` `Terminal::resize` with real cell metrics.
        self.term
            .lock()
            .resize(TermSize::new(cols as usize, rows as usize));
        self.listener.bump();
    }

    fn has_exited(&self) -> bool {
        self.listener.has_exited()
    }

    fn generation(&self) -> u64 {
        self.listener.generation()
    }
}

// The 16 ANSI colors (a standard dark palette) + default fg/bg. We resolve named
// colors against this fixed palette and indexed colors against the xterm 256
// ramp, rather than threading a full theme through — a self-contained, good-
// looking default. (A theme can be layered later by replacing this table.)
pub const DEFAULT_FG: Rgba = Rgba::new(0xd6, 0xd6, 0xd6);
pub const DEFAULT_BG: Rgba = Rgba::new(0x14, 0x14, 0x18);

const ANSI_16: [Rgba; 16] = [
    Rgba::new(0x1c, 0x1c, 0x22), // black
    Rgba::new(0xe0, 0x50, 0x50), // red
    Rgba::new(0x52, 0xc0, 0x6a), // green
    Rgba::new(0xd4, 0xb0, 0x4a), // yellow
    Rgba::new(0x4a, 0x8c, 0xe0), // blue
    Rgba::new(0xb0, 0x6a, 0xd6), // magenta
    Rgba::new(0x4a, 0xc0, 0xc8), // cyan
    Rgba::new(0xd6, 0xd6, 0xd6), // white
    Rgba::new(0x55, 0x55, 0x5e), // bright black
    Rgba::new(0xff, 0x6e, 0x6e), // bright red
    Rgba::new(0x6e, 0xe0, 0x86), // bright green
    Rgba::new(0xff, 0xd0, 0x66), // bright yellow
    Rgba::new(0x6e, 0xa8, 0xff), // bright blue
    Rgba::new(0xd0, 0x86, 0xff), // bright magenta
    Rgba::new(0x6e, 0xe0, 0xe8), // bright cyan
    Rgba::new(0xff, 0xff, 0xff), // bright white
];

fn rgb(r: Rgb) -> Rgba {
    Rgba::new(r.r, r.g, r.b)
}

fn resolve_color(
    color: Color,
    colors: &alacritty_terminal::term::color::Colors,
    is_fg: bool,
) -> Rgba {
    match color {
        Color::Spec(r) => rgb(r),
        Color::Named(named) => named_color(named, is_fg),
        Color::Indexed(idx) => {
            // Prefer the live palette if the terminal program set it (OSC 4),
            // else fall back to the standard xterm-256 ramp.
            if let Some(c) = colors[idx as usize] {
                rgb(c)
            } else {
                indexed_256(idx)
            }
        }
    }
}

fn named_color(named: NamedColor, _is_fg: bool) -> Rgba {
    match named {
        NamedColor::Black => ANSI_16[0],
        NamedColor::Red => ANSI_16[1],
        NamedColor::Green => ANSI_16[2],
        NamedColor::Yellow => ANSI_16[3],
        NamedColor::Blue => ANSI_16[4],
        NamedColor::Magenta => ANSI_16[5],
        NamedColor::Cyan => ANSI_16[6],
        NamedColor::White => ANSI_16[7],
        NamedColor::BrightBlack => ANSI_16[8],
        NamedColor::BrightRed => ANSI_16[9],
        NamedColor::BrightGreen => ANSI_16[10],
        NamedColor::BrightYellow => ANSI_16[11],
        NamedColor::BrightBlue => ANSI_16[12],
        NamedColor::BrightMagenta => ANSI_16[13],
        NamedColor::BrightCyan => ANSI_16[14],
        NamedColor::BrightWhite => ANSI_16[15],
        NamedColor::Foreground | NamedColor::BrightForeground => DEFAULT_FG,
        NamedColor::Background => DEFAULT_BG,
        NamedColor::Cursor => DEFAULT_FG,
        NamedColor::DimBlack => ANSI_16[0],
        NamedColor::DimRed => ANSI_16[1],
        NamedColor::DimGreen => ANSI_16[2],
        NamedColor::DimYellow => ANSI_16[3],
        NamedColor::DimBlue => ANSI_16[4],
        NamedColor::DimMagenta => ANSI_16[5],
        NamedColor::DimCyan => ANSI_16[6],
        NamedColor::DimWhite => ANSI_16[7],
        NamedColor::DimForeground => DEFAULT_FG,
    }
}

/// Standard xterm 256-color ramp: 0-15 ANSI, 16-231 6×6×6 cube, 232-255 grays.
fn indexed_256(idx: u8) -> Rgba {
    match idx {
        0..=15 => ANSI_16[idx as usize],
        16..=231 => {
            let i = idx - 16;
            let r = i / 36;
            let g = (i % 36) / 6;
            let b = i % 6;
            let conv = |v: u8| -> u8 {
                if v == 0 {
                    0
                } else {
                    (v as u16 * 40 + 55) as u8
                }
            };
            Rgba::new(conv(r), conv(g), conv(b))
        }
        232..=255 => {
            let v = (idx - 232) * 10 + 8;
            Rgba::new(v, v, v)
        }
    }
}
