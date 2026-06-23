//! The cockpit-surface adapter — mount the [`Editor`] as a dock pane in
//! starbridge-v2.
//!
//! starbridge-v2's dock hosts any [`CockpitSurface`] (the slim ~8-method item
//! trait in `starbridge-v2/src/dock/surface.rs`). This module gives the editor
//! everything that trait needs, as a concrete [`EditorSurface`] handle.
//!
//! ## Two-file delivery (no heavy cockpit.rs touch)
//!
//! deos-zed is its own workspace, so it can't `use` starbridge-v2's
//! `CockpitSurface` trait directly. The split is:
//!
//!   * **here** — [`EditorSurface`], a concrete handle holding the editor
//!     [`Entity`] plus a `FileTree`, exposing `tab_label` / `render_body` /
//!     `focus_handle` / `is_dirty` / `item_id` as plain inherent methods. This is
//!     the real, tested logic.
//!   * **`starbridge-v2/src/dock/editor_surface.rs`** (delivered ready-to-drop) —
//!     a ~20-line `impl CockpitSurface for EditorSurface` that forwards each
//!     trait method to the inherent method here. It lives in starbridge-v2
//!     because that is where the trait lives; mounting it is a one-line
//!     `pub mod editor_surface;` in `dock/mod.rs` (the dock module, NOT
//!     cockpit.rs) plus a `deos-zed` path dependency.
//!
//! Because both crates pin the same gpui fork, the `Entity<Editor>` here is
//! byte-identical to the one starbridge-v2 sees — the forward is a plain call,
//! no glue.

use std::path::PathBuf;
use std::sync::Arc;

use gpui::{
    div, AnyElement, App, AppContext as _, Entity, FocusHandle, IntoElement, ParentElement as _,
    SharedString, Styled as _, Window,
};
use gpui_component::h_flex;

use crate::editor::Editor;
use crate::file_tree::FileTree;
use crate::fs::Fs;

/// A mounted editor: the editor entity + a side file tree, addressable by a
/// stable surface id. Hand this to `starbridge-v2`'s `CockpitSurface` impl.
///
/// When built firmament-backed ([`EditorSurface::firmament`]) the surface also
/// keeps the TYPED `Arc<FirmamentFs>` handle so the host can read the live
/// receipt log (the `N saves · on-ledger` chrome reflects REAL `TurnReceipt`s,
/// not a disk write). The `Arc<dyn Fs>` the editor + tree hold is the SAME
/// object — one ledger, one save path.
#[derive(Clone)]
pub struct EditorSurface {
    id: u64,
    editor: Entity<Editor>,
    tree: Arc<FileTree>,
    /// The typed firmament handle, when this surface is firmament-backed. Lets
    /// the host surface the live receipt count (the real on-ledger save count)
    /// rather than re-deriving it from the gpui-side document patch history.
    #[cfg(feature = "firmament")]
    firmament: Option<Arc<crate::fs::FirmamentFs>>,
}

impl EditorSurface {
    /// Build an editor surface over the [`Fs`] seam, rooted at `root` for the
    /// file tree. `id` is the stable surface identity within a pane (the host
    /// supplies a monotonic counter or a `Tab` discriminant).
    pub fn new(
        id: u64,
        fs: Arc<dyn Fs>,
        root: PathBuf,
        window: &mut Window,
        cx: &mut App,
    ) -> Self {
        let editor = cx.new(|cx| Editor::new(fs.clone(), window, cx));
        let tree = Arc::new(FileTree::new(fs, root, cx));
        Self {
            id,
            editor,
            tree,
            #[cfg(feature = "firmament")]
            firmament: None,
        }
    }

    /// Wrap an already-built editor entity (e.g. one the host opened a file in)
    /// with a file tree.
    pub fn from_editor(id: u64, editor: Entity<Editor>, tree: Arc<FileTree>) -> Self {
        Self {
            id,
            editor,
            tree,
            #[cfg(feature = "firmament")]
            firmament: None,
        }
    }

    /// **Build a FIRMAMENT-BACKED editor surface** — the cockpit-default mount:
    /// the editor edits SOVEREIGN CELLS over an in-process `Ledger` +
    /// `TurnExecutor`, and every save is a real cap-gated `SetField` turn leaving
    /// a verifiable [`TurnReceipt`](dregg_turn::TurnReceipt). No disk is touched.
    ///
    /// The mount seeds a small project of file-cells (`files`: `(path, content)`),
    /// grants the editor the per-file edit caps, opens the FIRST file THROUGH THE
    /// EDITOR's own `open()` (so the buffer the user sees is the cell's committed
    /// content, decoded from its `fields_map`), and roots the file tree at
    /// `root` over the SAME firmament fs (the left rail browses the cells, not
    /// disk). The returned surface keeps the typed `FirmamentFs` so the host can
    /// read the live receipt log.
    ///
    /// This is the PER-EDITOR mount: a firmament fs over a FRESH `OwnedSpine`
    /// (its own ledger + executor). It is the headless / test / no-live-World
    /// default. A host with a live cockpit `World` it wants edits to land on
    /// mounts [`EditorSurface::firmament_over`] instead, handing the spine that
    /// wraps the live World — then the editor edits the SAME ledger the cockpit
    /// inspects.
    #[cfg(feature = "firmament")]
    pub fn firmament(
        id: u64,
        root: PathBuf,
        files: &[(&str, &str)],
        window: &mut Window,
        cx: &mut App,
    ) -> anyhow::Result<Self> {
        Self::firmament_over(
            id,
            Arc::new(crate::fs::FirmamentFs::new()),
            root,
            files,
            window,
            cx,
        )
    }

    /// **Mount a firmament-backed editor surface OVER an existing FirmamentFs** —
    /// the cockpit seam. The caller builds the [`FirmamentFs`](crate::fs::FirmamentFs)
    /// (via [`FirmamentFs::over`](crate::fs::FirmamentFs::over) the live cockpit
    /// spine, or [`FirmamentFs::new`](crate::fs::FirmamentFs::new) for a fresh
    /// one), then this seeds the `files` onto THAT fs's ledger, opens the first
    /// through the editor's real `open()`, and roots the tree over it. When `firm`
    /// is mounted over the live `World`, a save lands on the ledger the cockpit's
    /// cell inspector reads — one ledger, one save path.
    #[cfg(feature = "firmament")]
    pub fn firmament_over(
        id: u64,
        firm: Arc<crate::fs::FirmamentFs>,
        root: PathBuf,
        files: &[(&str, &str)],
        window: &mut Window,
        cx: &mut App,
    ) -> anyhow::Result<Self> {
        for (path, content) in files {
            firm.seed_file(*path, content)?;
        }
        let fs: Arc<dyn Fs> = firm.clone();

        // Open the first seeded file THROUGH the editor's real `open()` path so
        // the buffer is the cell's decoded content (not a seeded in-memory
        // string) — the SAME code path the running pane uses on a tree click.
        let first = files.first().map(|(p, _)| PathBuf::from(*p));
        let editor = cx.new(|cx| {
            let mut ed = Editor::new(fs.clone(), window, cx);
            if let Some(path) = first {
                if let Err(e) = ed.open(path, window, cx) {
                    eprintln!("firmament editor: could not open seed cell: {e:#}");
                }
            }
            ed
        });
        let tree = Arc::new(FileTree::new(fs, root, cx));
        Ok(Self {
            id,
            editor,
            tree,
            firmament: Some(firm),
        })
    }

    /// The typed firmament handle, if this surface is firmament-backed — lets the
    /// host read the live on-ledger save count / last receipt.
    #[cfg(feature = "firmament")]
    pub fn firmament_fs(&self) -> Option<&Arc<crate::fs::FirmamentFs>> {
        self.firmament.as_ref()
    }

    /// The number of real `TurnReceipt`s the firmament ledger has recorded (the
    /// genuine on-ledger save count), or `None` if this surface is not
    /// firmament-backed.
    #[cfg(feature = "firmament")]
    pub fn receipt_count(&self) -> Option<usize> {
        self.firmament.as_ref().map(|f| f.receipt_count())
    }

    /// Build a SEEDED editor surface: an editor whose buffer is filled in-memory
    /// with `revisions` (the last is shown; each prior one is an on-ledger patch)
    /// under the virtual `name` (drives the highlighter language), plus a real
    /// file tree over `fs`/`root`. Deterministic and disk-free for the buffer —
    /// exactly what the headless showcase bake wants (syntax-highlighted code with
    /// a real `N patches · on-ledger` status, no file to load). The tree still
    /// reflects `fs`/`root` so the left rail shows a real project.
    pub fn seeded(
        id: u64,
        fs: Arc<dyn Fs>,
        root: PathBuf,
        name: &str,
        revisions: &[&str],
        window: &mut Window,
        cx: &mut App,
    ) -> Self {
        let editor = cx.new(|cx| {
            let mut ed = Editor::new(fs.clone(), window, cx);
            ed.seed_content(name, revisions, window, cx);
            ed
        });
        let tree = Arc::new(FileTree::new(fs, root, cx));
        Self {
            id,
            editor,
            tree,
            #[cfg(feature = "firmament")]
            firmament: None,
        }
    }

    /// The underlying editor entity, for host-side open/save calls.
    pub fn editor(&self) -> &Entity<Editor> {
        &self.editor
    }

    // --- the methods the host's `CockpitSurface` impl forwards to ------------

    /// `CockpitSurface::item_id` payload.
    pub fn surface_id(&self) -> u64 {
        self.id
    }

    /// `CockpitSurface::tab_label`: the document title (filename + dirty dot).
    pub fn tab_label(&self, cx: &App) -> SharedString {
        self.editor.read(cx).title()
    }

    /// `CockpitSurface::is_dirty`: unsaved edits in the buffer.
    pub fn is_dirty(&self, cx: &App) -> bool {
        self.editor.read(cx).is_dirty()
    }

    /// `CockpitSurface::focus_handle`: the editor's focus handle.
    pub fn focus_handle(&self, cx: &App) -> FocusHandle {
        self.editor.read(cx).focus_handle(cx)
    }

    /// `CockpitSurface::render_body`: file tree on the left, editor on the
    /// right. Returns an `AnyElement` so the host trait stays object-safe.
    pub fn render_body(&mut self, _window: &mut Window, cx: &mut App) -> AnyElement {
        let editor = self.editor.clone();
        // Clicking a tree file opens it into THIS surface's editor.
        let open_editor = self.editor.clone();
        let tree_el = self.tree.render(
            self.editor.clone(),
            move |ed: &mut Editor, path, window, cx| {
                let _ = ed.open(path, window, cx);
            },
            cx,
        );
        // NOTE: the tree's host view is the Editor entity itself, so on-open
        // runs in the editor's own context — no extra wiring.
        let _ = open_editor;

        // `flex_1().min_h(0).min_w(0)` on the row (in addition to `size_full`) makes
        // the body claim its parent's full measured height robustly whether the
        // pane is laid out in a flex COLUMN (showcase) or directly in a flex ROW
        // (self-hosting) — a bare `size_full` here left the editor body 0-height in
        // the single-row self-hosting bake, so the InputState had no visible lines
        // to paint (the dark/empty editor body). The tree + editor columns carry
        // `min_h(0)` so they too resolve a definite height to fill.
        h_flex()
            .size_full()
            .flex_1()
            .min_h(gpui::px(0.))
            .min_w(gpui::px(0.))
            .child(
                div()
                    .w(gpui::px(220.))
                    .h_full()
                    .min_h(gpui::px(0.))
                    .child(tree_el),
            )
            .child(
                div()
                    .flex_1()
                    .h_full()
                    .min_h(gpui::px(0.))
                    .min_w(gpui::px(0.))
                    .child(editor),
            )
            .into_any_element()
    }
}
