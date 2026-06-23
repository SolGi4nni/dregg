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
#[derive(Clone)]
pub struct EditorSurface {
    id: u64,
    editor: Entity<Editor>,
    tree: Arc<FileTree>,
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
        Self { id, editor, tree }
    }

    /// Wrap an already-built editor entity (e.g. one the host opened a file in)
    /// with a file tree.
    pub fn from_editor(id: u64, editor: Entity<Editor>, tree: Arc<FileTree>) -> Self {
        Self { id, editor, tree }
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
        Self { id, editor, tree }
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

        h_flex()
            .size_full()
            .child(div().w(gpui::px(220.)).h_full().child(tree_el))
            .child(div().flex_1().h_full().child(editor))
            .into_any_element()
    }
}
