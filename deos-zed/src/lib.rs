//! # deos-zed — a real code editor as a deos surface
//!
//! deos-zed is the editor half of the self-hosting deos dev loop: it edits real
//! files inside deos, with the firmament seam ready so file I/O can later route
//! through capability-checked, receipted dregg turns instead of `std::fs`.
//!
//! ## The three pieces
//!
//! * [`fs`] — the [`Fs`](fs::Fs) seam. The ONE place deos-zed touches a
//!   filesystem. [`RealFs`](fs::RealFs) (std::fs) ships today; [`FirmamentFs`](fs::FirmamentFs)
//!   (file = cell, save = receipted turn) is the documented next-step impl. The
//!   editor depends only on the trait, so the firmament swap is one impl.
//! * [`editor`] — the [`Editor`](editor::Editor) surface: a rope-backed,
//!   syntax-highlighting code editor (gpui-component's `InputState`) whose
//!   open/save go through the seam, tracking open path + dirty state.
//! * [`file_tree`] — the [`FileTree`](file_tree::FileTree) affordance: browse a
//!   directory (via the seam) and click a file to open it into the editor.
//!
//! ## The editor buffer IS a document-language document
//!
//! The editor's buffer is the materialized fold of a [`dregg_doc::RopeDoc`] — a
//! Pijul-shaped patch [`History`](dregg_doc::History). Opening a file starts a
//! document; each save accrues a verifiable [`Patch`](dregg_doc::Patch) (not an
//! overwrite of bytes), so the durable form is the provenance-bearing patch
//! history. [`doc_viewer`] is the inspecting face: it renders a document's BLAME /
//! timeline and its CONFLICT OBJECTS (two pens at one tail shown as both
//! alternatives + authorship, never a `<<<<<<<` text wound). See
//! [`Editor::document`](editor::Editor::document), [`Editor::blame`](editor::Editor::blame),
//! and [`DocViewer`](doc_viewer::DocViewer).
//!
//! ## Mounting in deos
//!
//! [`cockpit_surface`] holds the adapter that lets the editor live as a tab in
//! starbridge-v2's dock. See [`cockpit_surface::EditorSurface`] and the
//! ready-to-drop `starbridge-v2/src/dock/editor_surface.rs`.
//!
//! ## Approach
//!
//! This crate leans on **gpui-component's code editor** (option (a) in the
//! Zed-in-deos investigation): a rope-backed `Input` in `code_editor` mode with
//! tree-sitter highlighting (33 grammars available; rust/json/toml/markdown on
//! by default). That is the lightest capable path — Zed's full `editor` crate is
//! huge and coupled to project/lsp/multibuffer; gpui-component gives
//! open/edit/save/highlight + a file tree + a dock out of the box, on the SAME
//! gpui fork the cockpit pins, so one gpui resolves across the whole graph.

pub mod doc_viewer;
pub mod editor;
pub mod file_tree;
pub mod fs;

#[cfg(feature = "cockpit-surface")]
pub mod cockpit_surface;

#[cfg(feature = "screenshot")]
pub mod screenshot;

pub use doc_viewer::DocViewer;
pub use editor::Editor;
pub use file_tree::FileTree;
pub use fs::{DirEntry, FirmamentFs, Fs, Metadata, RealFs};
