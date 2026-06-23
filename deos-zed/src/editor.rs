//! The editor surface — a rope-backed, syntax-highlighting code editor over the
//! [`Fs`] seam.
//!
//! Built on gpui-component's `InputState`/`Input` in code-editor mode: a real
//! rope buffer (multi-line, cursor, selection, undo/redo, line numbers, indent
//! guides, soft wrap) with tree-sitter syntax highlighting. The ONE thing this
//! module adds on top is that open/save go through [`Fs`] (not `std::fs`), and
//! it tracks the open path + dirty state so the editor is a real document, not a
//! scratch buffer.

use std::path::{Path, PathBuf};
use std::sync::Arc;

use anyhow::Result;
use dregg_doc::{Author, BlameLine, Granularity, Rendered, RopeDoc};
use gpui::{
    div, px, App, AppContext as _, Context, Entity, FocusHandle, Focusable, IntoElement,
    ParentElement as _, Render, SharedString, Styled as _, Subscription, Window,
};
use gpui_component::input::{Input, InputEvent, InputState, TabSize};
use gpui_component::{ActiveTheme as _, StyledExt as _};
use ropey::Rope;

use crate::fs::Fs;

/// Map a file extension to a gpui-component highlighter language name. Returns
/// `"text"` (the plain, no-grammar language) for anything unrecognized — the
/// editor still works, just without colour.
pub fn language_for_path(path: &Path) -> &'static str {
    match path
        .extension()
        .and_then(|e| e.to_str())
        .unwrap_or("")
        .to_ascii_lowercase()
        .as_str()
    {
        "rs" => "rust",
        "json" => "json",
        "toml" => "toml",
        "md" | "markdown" => "markdown",
        "js" | "mjs" | "cjs" => "javascript",
        "ts" => "typescript",
        "tsx" => "tsx",
        "jsx" => "javascript",
        "py" => "python",
        "go" => "go",
        "c" | "h" => "c",
        "cpp" | "cc" | "cxx" | "hpp" => "cpp",
        "html" | "htm" => "html",
        "css" => "css",
        "sh" | "bash" => "bash",
        "yaml" | "yml" => "yaml",
        "sql" => "sql",
        "lua" => "lua",
        "rb" => "ruby",
        "java" => "java",
        "kt" | "kts" => "kotlin",
        "swift" => "swift",
        "zig" => "zig",
        "lean" => "text", // no lean grammar in the registry yet; plain is fine
        _ => "text",
    }
}

/// A live document open in the editor: the rope-backed input state plus the path
/// it was loaded from and whether it has unsaved edits.
///
/// ## The buffer IS a document-language document
///
/// The visible `input` rope is the FAST interactive cache; the *durable* form of
/// what's open is a [`dregg_doc::RopeDoc`] — a patch [`History`](dregg_doc::History)
/// whose fold materializes the buffer. [`Editor::open`] starts a `RopeDoc` from the
/// loaded content; every [`Editor::save`] hands the current buffer to
/// `RopeDoc::edit_rope`, which diffs it against the document's content and accrues
/// the minimal `Add`/`Delete`/`Connect` [`Patch`](dregg_doc::Patch). So saves do
/// not overwrite bytes — they EXTEND a verifiable patch history, queryable for
/// [`Editor::blame`] and [`Editor::rendered`] (conflicts as first-class objects).
/// The `Fs` save still writes the materialized bytes (so disk stays readable);
/// the patch history is the document's real, provenance-bearing form.
pub struct Editor {
    /// The rope-backed code input (gpui-component). Holds the actual text,
    /// cursor, selection, undo history, highlighting.
    pub input: Entity<InputState>,
    /// The [`Fs`] seam every file op goes through. Swap this `Arc` for a
    /// `FirmamentFs` and the editor edits cells instead of disk — no other
    /// change.
    fs: Arc<dyn Fs>,
    /// The path currently open, if any.
    path: Option<PathBuf>,
    /// `true` when the buffer differs from what was last loaded/saved.
    dirty: bool,
    /// A short status message shown under the editor (last save result, errors).
    status: SharedString,
    /// The durable document: a patch [`History`](dregg_doc::History) of which the
    /// buffer is the materialized fold. `None` until a file is opened. Each save
    /// commits a [`Patch`](dregg_doc::Patch) here; blame/timeline/conflicts are
    /// read off it.
    doc: Option<RopeDoc>,
    /// The authoring identity stamped onto patches this editor commits (who wrote
    /// what). Distinct editors (co-authors) use distinct ids so blame + conflict
    /// attribution are real.
    author: Author,
    _subscriptions: Vec<Subscription>,
}

impl Editor {
    /// Create an empty editor over the given filesystem seam.
    pub fn new(fs: Arc<dyn Fs>, window: &mut Window, cx: &mut Context<Self>) -> Self {
        let input = cx.new(|cx| {
            InputState::new(window, cx)
                .code_editor("text")
                .line_number(true)
                .indent_guides(true)
                .tab_size(TabSize {
                    tab_size: 4,
                    hard_tabs: false,
                })
                .soft_wrap(false)
                .placeholder("Open a file to begin…")
        });

        // Any edit to the buffer marks the document dirty.
        let subs = vec![cx.subscribe(&input, |this, _input, event: &InputEvent, cx| {
            if matches!(event, InputEvent::Change) {
                if !this.dirty {
                    this.dirty = true;
                    cx.notify();
                }
            }
        })];

        let label = fs.backend_label();
        Self {
            input,
            fs,
            path: None,
            dirty: false,
            status: SharedString::from(format!("ready — {label}")),
            doc: None,
            author: Author(1),
            _subscriptions: subs,
        }
    }

    /// Set the authoring identity stamped onto the patches this editor commits.
    /// Co-authoring editors use distinct ids so blame + conflict attribution are
    /// real ("who wrote which alternative" is a fact, not a guess).
    pub fn with_author(mut self, author: Author) -> Self {
        self.author = author;
        self
    }

    /// The authoring identity this editor stamps onto its patches.
    pub fn author(&self) -> Author {
        self.author
    }

    /// The durable document (a patch [`History`](dregg_doc::History)) open in the
    /// editor, if any. The buffer is its materialized fold; this is the real,
    /// provenance-bearing form — query it for blame/timeline/conflicts.
    pub fn document(&self) -> Option<&RopeDoc> {
        self.doc.as_ref()
    }

    /// Per-atom blame for the open document, in document order: who authored each
    /// live span, in which patch. Empty if no document is open. Correct by
    /// construction (attribution rides the content-addressed atom, never a line
    /// position — it does not smear when surrounding text moves).
    pub fn blame(&self) -> Vec<BlameLine> {
        self.doc.as_ref().map(|d| d.blame()).unwrap_or_default()
    }

    /// The full rendered structure of the open document: clean runs AND
    /// first-class conflict regions (each alternative tagged with its author).
    /// `None` if no document is open. This is what the document VIEWER inspects.
    pub fn rendered(&self) -> Option<Rendered> {
        self.doc.as_ref().map(|d| d.rendered())
    }

    /// How many patches the open document's history holds (the save/edit count).
    pub fn patch_count(&self) -> usize {
        self.doc.as_ref().map(|d| d.history().len()).unwrap_or(0)
    }

    /// The path currently open, if any.
    pub fn path(&self) -> Option<&Path> {
        self.path.as_deref()
    }

    /// `true` when there are unsaved edits.
    pub fn is_dirty(&self) -> bool {
        self.dirty
    }

    /// The status line text (backend label, last save, errors).
    pub fn status(&self) -> SharedString {
        self.status.clone()
    }

    /// The display title for this document (filename + dirty marker).
    pub fn title(&self) -> SharedString {
        let name = self
            .path
            .as_ref()
            .and_then(|p| p.file_name())
            .and_then(|n| n.to_str())
            .unwrap_or("untitled");
        if self.dirty {
            SharedString::from(format!("● {name}"))
        } else {
            SharedString::from(name.to_string())
        }
    }

    /// The full current buffer text (rope → String).
    pub fn text(&self, cx: &App) -> String {
        self.input.read(cx).value().to_string()
    }

    /// Open a file through the [`Fs`] seam: load its content, set the
    /// highlighter language from the extension, and replace the buffer. Returns
    /// any load error so callers can surface it.
    pub fn open(&mut self, path: PathBuf, window: &mut Window, cx: &mut Context<Self>) -> Result<()> {
        let content = self.fs.load(&path)?;
        let lang = language_for_path(&path);
        self.input.update(cx, |state, cx| {
            state.set_highlighter(lang, cx);
            state.set_value(content.clone(), window, cx);
        });
        // Start the durable document: a fresh patch-history whose genesis patch
        // is the loaded content (authored by this editor). The buffer the user
        // sees is exactly this document's fold. Line granularity is the spec's
        // span-coarse default (§4.4).
        let mut doc = RopeDoc::new(Granularity::Line);
        doc.edit_rope(self.author, &Rope::from_str(&content));
        self.doc = Some(doc);
        let name = path
            .file_name()
            .and_then(|n| n.to_str())
            .unwrap_or("file")
            .to_string();
        self.path = Some(path);
        self.dirty = false;
        self.status = SharedString::from(format!("opened {name} [{lang}] — 1 patch"));
        cx.notify();
        Ok(())
    }

    /// Seed the editor with in-memory content for a DETERMINISTIC headless render
    /// (the showcase bake): set the buffer + the highlighter language from the
    /// virtual `name`, and build a small on-ledger patch history so `patch_count`
    /// and `status` read like a real, edited-and-committed document — with NO
    /// disk/Fs round-trip. `revisions` are applied in order as successive patches
    /// (each a committed turn), the last being what the buffer shows; pass at least
    /// one. The status reads `<name> · <N> patches · on-ledger`.
    pub fn seed_content(
        &mut self,
        name: &str,
        revisions: &[&str],
        window: &mut Window,
        cx: &mut Context<Self>,
    ) {
        let lang = language_for_path(Path::new(name));
        let shown = revisions.last().copied().unwrap_or("");
        self.input.update(cx, |state, cx| {
            state.set_highlighter(lang, cx);
            state.set_value(shown.to_string(), window, cx);
        });
        // Build the durable document by replaying the revisions as patches — each
        // `edit_rope` accrues a patch into the history (the genesis + edits), so
        // `patch_count()` reflects a real multi-commit document.
        let mut doc = RopeDoc::new(Granularity::Line);
        for rev in revisions {
            doc.edit_rope(self.author, &Rope::from_str(rev));
        }
        let patches = doc.history().len();
        self.doc = Some(doc);
        self.path = Some(PathBuf::from(name));
        self.dirty = false;
        self.status = SharedString::from(format!("{name} · {patches} patches · on-ledger"));
        cx.notify();
    }

    /// Save the buffer back through the [`Fs`] seam. With `RealFs` this writes
    /// disk; with `FirmamentFs` this is a receipted turn. Returns an error if no
    /// path is open or the save fails.
    pub fn save(&mut self, cx: &mut Context<Self>) -> Result<()> {
        let Some(path) = self.path.clone() else {
            self.status = SharedString::from("nothing to save (no file open)");
            cx.notify();
            anyhow::bail!("no file open");
        };
        let content = self.text(cx);
        // The save ACCRUES A PATCH: diff the current buffer against the durable
        // document's content and commit the minimal patch (the editor edit -> a
        // verifiable, provenance-bearing patch over the document history). This is
        // the editor-buffer-as-document weld — the durable form is the history,
        // not the bytes we also write to disk for readability.
        if let Some(doc) = self.doc.as_mut() {
            doc.edit_rope(self.author, &Rope::from_str(&content));
        }
        let patches = self.patch_count();
        match self.fs.save(&path, &content) {
            Ok(()) => {
                self.dirty = false;
                let name = path
                    .file_name()
                    .and_then(|n| n.to_str())
                    .unwrap_or("file")
                    .to_string();
                self.status = SharedString::from(format!(
                    "saved {name} ({} bytes) — {patches} patches",
                    content.len()
                ));
                cx.notify();
                Ok(())
            }
            Err(e) => {
                self.status = SharedString::from(format!("save FAILED: {e}"));
                cx.notify();
                Err(e)
            }
        }
    }

    /// The editor's focus handle (the underlying input's), so a host pane can
    /// focus it on activation.
    pub fn focus_handle(&self, cx: &App) -> FocusHandle {
        self.input.focus_handle(cx)
    }
}

impl Focusable for Editor {
    fn focus_handle(&self, cx: &App) -> FocusHandle {
        self.input.focus_handle(cx)
    }
}

impl Render for Editor {
    fn render(&mut self, _window: &mut Window, cx: &mut Context<Self>) -> impl IntoElement {
        div()
            .v_flex()
            .size_full()
            .child(
                // The code editor body fills the available space.
                div().flex_1().min_h(px(0.)).child(Input::new(&self.input).h_full()),
            )
            .child(
                // A slim status line: which backend, last save, dirty marker.
                div()
                    .h(px(22.))
                    .w_full()
                    .px_2()
                    .flex()
                    .items_center()
                    .gap_2()
                    .bg(cx.theme().secondary)
                    .text_xs()
                    .text_color(cx.theme().muted_foreground)
                    .child(self.title())
                    .child(div().flex_1())
                    .child(self.status())
                    .child(SharedString::from(self.fs.backend_label())),
            )
    }
}
