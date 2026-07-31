//! THE SELF-HOSTING LOOP, DEMONSTRATED — both real halves in one cockpit view.
//!
//! Unlike [`crate::showcase`] (which mounts *seeded* surfaces for a deterministic
//! marketing frame), this view mounts the GENUINE self-hosting dev loop and lets
//! the host DRIVE it + ASSERT the proofs:
//!
//!   * EDITOR — a [`EditorPane::firmament_over`] the LIVE cockpit `World`: the
//!     buffer is a sovereign cell, and [`SelfHostingView::fire_save`] sets the
//!     buffer text and calls the editor's real `save`, which commits a cap-gated
//!     `SetField` turn through the verified executor. The save count is the LIVE
//!     `TurnReceipt` count — read off the ledger, never a mock. This is half (a):
//!     **edit a source file → a real verified turn on the live ledger**.
//!
//!   * TERMINAL — a [`TerminalPane`] over a LIVE alacritty PTY running a real
//!     command (`cargo --version` by default). [`SelfHostingView::terminal_text`]
//!     scrapes the grid so the host can assert the command's genuine stdout landed
//!     in the cell grid. This is half (b): **a real terminal running real
//!     `cargo`/`git` INSIDE deos**.
//!
//! The two halves render side by side; the headless bake (`--render-self-hosting`
//! in `main.rs`) drives both, asserts both proofs, and captures the PNG.
//!
//! # The full loop (`--render-self-hosting-full`)
//!
//! The CELL/DISK gap — the editor saves to cells, `cargo`/`rustc` reads disk — is
//! closed by the FirmamentFs↔disk DUAL-WRITE. [`SelfHostingView::build_with_mirror`]
//! enables a disk-mirror root on the editor's firmament fs: after each save's
//! verified turn commits (the cell is the durable receipted source of truth), the
//! new content is ALSO written to `<mirror_root>/<path>` — a derived read-mirror
//! the legacy disk-reading toolchain compiles from. With the terminal pointed at
//! that same dir, the FULL single loop runs: editor edit → receipted turn → disk
//! mirror → terminal's `rustc`/`cargo` sees and compiles THAT VERY EDIT.

use std::cell::RefCell;
use std::rc::Rc;

use gpui::{
    div, px, App, AppContext, Context, Entity, FocusHandle, Focusable, InteractiveElement,
    IntoElement, ParentElement, Render, Styled, Window,
};

use crate::dock::editor_surface::EditorPane;
use crate::dock::surface::CockpitSurface;
use crate::dock::terminal_surface::TerminalPane;
use crate::world::World;

/// The palette is [`crate::views::theme`] — this file used to hold its own
/// transcription of the GitHub-dark hexes.
use crate::views::theme;

/// The seed project the firmament editor opens onto — file-cells installed on the
/// LIVE cockpit `World`. The first entry is opened in the buffer; saving it fires
/// a real cap-gated turn the cockpit's own cell inspector can see.
const SELF_HOSTING_SEED: &[(&str, &str)] = &[(
    "/main.rs",
    "// edit me — a save here is a RECEIPTED dregg turn on the LIVE cockpit ledger,\n\
     // dual-written to disk where the terminal's rustc compiles it.\n\
     fn main() {\n    println!(\"v1\");\n}\n",
)];

/// The namespace path of the seed source file the demo edits (the file-cell that
/// dual-writes to `<mirror_root>/main.rs`).
pub const SELF_HOSTING_SOURCE_PATH: &str = "/main.rs";

/// The root view that mounts BOTH real self-hosting halves.
pub struct SelfHostingView {
    editor: EditorPane,
    terminal: TerminalPane,
    /// The live cockpit `World` the editor saves into — the same ledger the
    /// receipt proof reads.
    world: Rc<RefCell<World>>,
    focus: FocusHandle,
}

impl SelfHostingView {
    /// Build the self-hosting view: a firmament editor over `world` + a live-PTY
    /// terminal running `shell_cmd` (program, args). Pass `None` for `$SHELL`.
    pub fn build(
        world: Rc<RefCell<World>>,
        terminal_cmd: Option<(String, Vec<String>)>,
        window: &mut Window,
        cx: &mut App,
    ) -> anyhow::Result<Self> {
        Self::build_with_mirror(world, terminal_cmd, None, window, cx)
    }

    /// Build the self-hosting view with an OPTIONAL disk-mirror root for the
    /// firmament editor — the FULL-LOOP wire. When `mirror_root` is `Some(dir)`,
    /// the editor's firmament fs dual-writes every receipted save to
    /// `<dir>/<path>` so a real terminal toolchain (cargo/git) reading disk sees
    /// the very edit the editor saved as a cell. `None` → cell-only (today's
    /// behavior). The cell is always the receipted source of truth; the disk file
    /// is a derived read-mirror.
    pub fn build_with_mirror(
        world: Rc<RefCell<World>>,
        terminal_cmd: Option<(String, Vec<String>)>,
        mirror_root: Option<std::path::PathBuf>,
        window: &mut Window,
        cx: &mut App,
    ) -> anyhow::Result<Self> {
        let root = std::env::current_dir().unwrap_or_else(|_| std::path::PathBuf::from("."));

        // EDITOR — firmament over the LIVE cockpit World: a save is a real turn on
        // the SAME ledger the receipt proof reads.
        let editor = EditorPane::firmament_over(
            1,
            world.clone(),
            root.clone(),
            SELF_HOSTING_SEED,
            window,
            cx,
        )?;

        // FULL-LOOP WIRE: if a mirror root was given, turn on the FirmamentFs↔disk
        // dual-write. Every receipted save now ALSO writes the new content to disk
        // under `mirror_root`, where the terminal's cargo/rustc reads it. This
        // closes the edit→receipted-turn→disk-mirror→toolchain-sees-it loop.
        if let Some(dir) = &mirror_root {
            let firm = editor
                .firmament_fs()
                .ok_or_else(|| anyhow::anyhow!("editor pane is not firmament-backed"))?;
            firm.enable_disk_mirror(dir.clone())?;
        }

        // TERMINAL — a LIVE PTY running a real command (or `$SHELL`). Real
        // alacritty PTY + grid; its output is genuine child-process stdout.
        let terminal = TerminalPane::spawn(2, terminal_cmd, cx)?;

        Ok(Self {
            editor,
            terminal,
            world,
            focus: cx.focus_handle(),
        })
    }

    /// The configured disk-mirror root of the firmament editor, if the dual-write
    /// is enabled — the directory the terminal toolchain reads the mirrored edits
    /// from.
    pub fn mirror_root(&self) -> Option<std::path::PathBuf> {
        self.editor.firmament_fs().and_then(|f| f.mirror_root())
    }

    /// HALF (a) — fire a REAL save: set the editor buffer to `content`, then call
    /// the editor's genuine `save`, which commits a cap-gated `SetField` turn
    /// through the verified executor. Returns the live on-ledger receipt count
    /// AFTER the save (a fresh `TurnReceipt` was recorded if it grew).
    pub fn fire_save(
        &self,
        content: &str,
        window: &mut Window,
        cx: &mut App,
    ) -> anyhow::Result<usize> {
        let editor = self.editor.editor().clone();
        editor.update(cx, |ed, cx| {
            ed.set_text(content, window, cx);
            ed.save(cx)
        })?;
        Ok(self.editor_receipt_count())
    }

    /// The live on-ledger receipt count of the editor's firmament ledger (the
    /// genuine `TurnReceipt` count — the real "N saves · on-ledger"). `0` if the
    /// pane somehow fell back off-firmament.
    pub fn editor_receipt_count(&self) -> usize {
        self.editor.receipt_count().unwrap_or(0)
    }

    /// The world's receipt count — proof the editor save landed on the SAME ledger
    /// the cockpit inspects (one ledger, one save path).
    pub fn world_receipt_count(&self) -> usize {
        self.world.borrow().receipts().len()
    }

    /// HALF (b) — write a line of input to the live PTY (e.g. a `cargo` command +
    /// `\n`), as if typed into the terminal.
    pub fn terminal_input(&self, s: &str, cx: &App) {
        self.terminal.view().read(cx).terminal.write_str(s);
    }

    /// Scrape the terminal grid into a single newline-joined string — the live
    /// child process's genuine on-grid output, for the host to assert against.
    pub fn terminal_text(&self, cx: &App) -> String {
        let content = self.terminal.view().read(cx).terminal.content();
        let cols = content.columns.max(1);
        let rows = content.screen_lines.max(1);
        // Reconstruct the visible grid from the sparse cell list.
        let mut grid = vec![vec![' '; cols]; rows];
        for cell in &content.cells {
            let line = cell.line;
            if line < 0 {
                continue;
            }
            let (r, c) = (line as usize, cell.column);
            if r < rows && c < cols {
                grid[r][c] = cell.c;
            }
        }
        grid.into_iter()
            .map(|row| row.into_iter().collect::<String>().trim_end().to_string())
            .collect::<Vec<_>>()
            .join("\n")
    }

    /// Has the live terminal child process exited (a one-shot command finished)?
    pub fn terminal_exited(&self, cx: &App) -> bool {
        self.terminal.view().read(cx).terminal.has_exited()
    }
}

impl Focusable for SelfHostingView {
    fn focus_handle(&self, _cx: &App) -> FocusHandle {
        self.focus.clone()
    }
}

impl Render for SelfHostingView {
    fn render(&mut self, window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        let editor_body = self.editor.render_body(window, cx);
        let terminal_body = self.terminal.render_body(window, cx);

        let receipts = self.world_receipt_count();
        let height = self.world.borrow().height();
        let cells = self.world.borrow().cell_count();

        let header = div()
            .flex()
            .items_center()
            .gap_3()
            .px_4()
            .py_2()
            .w_full()
            .bg(theme::panel())
            .border_b_1()
            .border_color(theme::border())
            .child(
                div()
                    .text_color(theme::accent())
                    .child("deos · self-hosting loop — develop dregg INSIDE deos"),
            )
            .child(badge(&format!("h{height}"), theme::accent()))
            .child(badge(&format!("{cells} cells"), theme::accent()))
            .child(badge(
                &format!("{receipts} receipts · on-ledger"),
                theme::accent(),
            ));

        let editor_pane = framed(
            "editor · deos-zed (firmament over the LIVE World)",
            "a save = a cap-gated SetField turn → a real TurnReceipt",
            editor_body,
        );
        let terminal_pane = framed(
            "terminal · deos-terminal (live alacritty PTY)",
            "real cargo/git running INSIDE deos",
            terminal_body,
        );

        div()
            .key_context("SelfHosting")
            .track_focus(&self.focus)
            .flex()
            .flex_col()
            .size_full()
            .bg(theme::bg())
            .text_color(theme::text())
            .font_family("Menlo")
            .child(header)
            .child(
                div()
                    .flex()
                    .gap_3()
                    .flex_1()
                    .min_h(px(0.))
                    .w_full()
                    .p_3()
                    .child(editor_pane)
                    .child(terminal_pane),
            )
    }
}

/// Mount the self-hosting view as a root view for the headless capture or a
/// windowed open.
pub fn build_root(
    world: Rc<RefCell<World>>,
    terminal_cmd: Option<(String, Vec<String>)>,
    window: &mut Window,
    cx: &mut App,
) -> anyhow::Result<Entity<SelfHostingView>> {
    build_root_with_mirror(world, terminal_cmd, None, window, cx)
}

/// Mount the self-hosting view with an OPTIONAL disk-mirror root (the FULL-LOOP
/// bake): the firmament editor dual-writes each receipted save to disk under
/// `mirror_root`, where the terminal's real toolchain reads it.
pub fn build_root_with_mirror(
    world: Rc<RefCell<World>>,
    terminal_cmd: Option<(String, Vec<String>)>,
    mirror_root: Option<std::path::PathBuf>,
    window: &mut Window,
    cx: &mut App,
) -> anyhow::Result<Entity<SelfHostingView>> {
    let view = cx.new(|cx| {
        SelfHostingView::build_with_mirror(world, terminal_cmd, mirror_root, window, cx)
            .expect("self-hosting view mount")
    });
    view.update(cx, |v, cx| {
        let focus = v.focus.clone();
        focus.focus(window, cx);
    });
    Ok(view)
}

fn badge(text: &str, color: gpui::Hsla) -> impl IntoElement {
    div()
        .px_2()
        .py_1()
        .rounded_md()
        .bg(theme::panel_hi())
        .border_1()
        .border_color(theme::border())
        .text_color(color)
        .text_xs()
        .child(text.to_string())
}

fn framed(title: &str, subtitle: &str, body: gpui::AnyElement) -> impl IntoElement {
    div()
        .flex()
        .flex_col()
        .flex_1()
        .min_w(px(0.))
        .h_full()
        .rounded_md()
        .border_1()
        .border_color(theme::border())
        .bg(theme::panel())
        .child(
            div()
                .flex()
                .flex_col()
                .gap_0p5()
                .px_3()
                .py_2()
                .border_b_1()
                .border_color(theme::border())
                .child(div().text_color(theme::text()).child(title.to_string()))
                .child(
                    div()
                        .text_xs()
                        .text_color(theme::muted())
                        .child(subtitle.to_string()),
                ),
        )
        .child(div().flex_1().min_h(px(0.)).overflow_hidden().child(body))
}
