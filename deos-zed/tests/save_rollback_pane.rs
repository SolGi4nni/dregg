//! THE SAVE-ROLLBACK test (backlog #6): a REFUSED / FAILED `Fs::save` must NOT
//! accrue a patch. The editor's marquee thesis is receipts↔patches — a patch
//! exists IFF the save committed. Before the fix, `Editor::save` called
//! `doc.edit_rope` (accruing the patch + advancing `patch_count`) UNCONDITIONALLY
//! before `fs.save`, and the `Err` arm never rolled it back: a refused cap-save
//! left a phantom patch with no receipt, drifting the Structure and Ledger faces.
//!
//! This drives the REAL gpui `Editor` in a headless gpui app over a deliberately
//! failing `Fs` and asserts the refused save leaves `patch_count()` (and the
//! document history) UNCHANGED — no phantom patch.
//!
//! Gated on `gui` (the gpui editor) + `screenshot` (the headless harness —
//! `HeadlessAppContext` + offscreen renderer + no-system-fonts text). Run with:
//!   cargo test --features "gui screenshot" --test save_rollback_pane

#![cfg(all(feature = "gui", feature = "screenshot"))]

use std::borrow::Cow;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use anyhow::{anyhow, Result};
use gpui::{
    div, px, size, AppContext as _, Context, Entity, HeadlessAppContext, IntoElement,
    PlatformTextSystem, Render, Window,
};
use gpui_wgpu::CosmicTextSystem;

use deos_zed::fs::{DirEntry, Fs, Metadata};
use deos_zed::Editor;

// The same OFL fonts the screenshot harness ships, so text shaping is real and
// deterministic with no system fonts.
static LILEX: &[u8] = include_bytes!("../assets/fonts/Lilex-Regular.ttf");
static IBM_PLEX: &[u8] = include_bytes!("../assets/fonts/IBMPlexSans-Regular.ttf");

/// An `Fs` whose `load` SUCCEEDS (so a document can open with its genesis patch)
/// but whose `save` ALWAYS fails — the in-band "cap-save refused / write failed"
/// outcome the rollback must survive. Everything else is inert (never reached
/// before the failing save).
struct FailingFs {
    seed: String,
}

impl Fs for FailingFs {
    fn load(&self, _path: &Path) -> Result<String> {
        Ok(self.seed.clone())
    }
    fn save(&self, _path: &Path, _content: &str) -> Result<()> {
        Err(anyhow!("cap-save refused (test)"))
    }
    fn read_dir(&self, _path: &Path) -> Result<Vec<DirEntry>> {
        Ok(Vec::new())
    }
    fn metadata(&self, _path: &Path) -> Result<Metadata> {
        Ok(Metadata {
            is_dir: false,
            is_symlink: false,
            len: self.seed.len() as u64,
        })
    }
    fn backend_label(&self) -> &'static str {
        "failing-fs (test)"
    }
}

/// A trivial gpui root view holding the editor entity, so we can drive it through
/// `editor.update(cx, …)` (the running pane's own path) in a headless window.
struct Holder {
    editor: Entity<Editor>,
}

impl Render for Holder {
    fn render(&mut self, _window: &mut Window, _cx: &mut Context<Self>) -> impl IntoElement {
        div()
    }
}

#[test]
fn a_refused_save_accrues_no_patch() {
    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system
        .add_fonts(vec![Cow::Borrowed(LILEX), Cow::Borrowed(IBM_PLEX)])
        .expect("load fonts");

    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(gpui_component::init);

    let path = "/deos/main.rs";
    let seed = "fn main() {\n    println!(\"before\");\n}\n";
    let edited = "fn main() {\n    println!(\"AFTER — but the save is refused\");\n}\n";

    #[allow(clippy::arc_with_non_send_sync)]
    let fs: Arc<dyn Fs> = Arc::new(FailingFs {
        seed: seed.to_string(),
    });

    // Build the REAL gpui Editor in a headless window (the same entity the pane holds).
    let window = cx
        .open_window(size(px(900.), px(600.)), |window, cx| {
            cx.new(|cx| {
                let editor = cx.new(|cx| Editor::new(fs.clone(), window, cx));
                Holder { editor }
            })
        })
        .expect("headless window");

    cx.run_until_parked();

    // Open the file: the genesis patch is the loaded content -> patch_count == 1.
    window
        .update(&mut cx, |holder, window, cx| {
            let editor = holder.editor.clone();
            editor.update(cx, |ed, cx| {
                ed.open(PathBuf::from(path), window, cx)
                    .expect("open the seed");
                assert_eq!(ed.patch_count(), 1, "open seeds exactly the genesis patch");
            });
        })
        .unwrap();

    cx.run_until_parked();

    // Edit the buffer, then attempt to save. The save is REFUSED by the failing Fs.
    window
        .update(&mut cx, |holder, window, cx| {
            let editor = holder.editor.clone();
            editor.update(cx, |ed, cx| {
                ed.set_text(edited, window, cx);
                let before = ed.patch_count();
                let history_before = ed.document().map(|d| d.history().len());
                assert_eq!(before, 1, "still one patch after an unsaved edit");

                let result = ed.save(cx);

                // The refusal is a VALUE (Err), never a panic — no turn committed.
                assert!(result.is_err(), "the failing Fs surfaces the save as Err");

                // THE ROLLBACK INVARIANT: no phantom patch. `patch_count` and the
                // document history are UNCHANGED by a refused save.
                assert_eq!(
                    ed.patch_count(),
                    before,
                    "a refused save accrues NO patch (patch_count unchanged)"
                );
                assert_eq!(
                    ed.document().map(|d| d.history().len()),
                    history_before,
                    "the document history is untouched by a refused save"
                );
                assert_eq!(
                    ed.patch_count(),
                    1,
                    "still just the genesis patch — no receipt, so no patch"
                );

                // The edit is not lost (still dirty, buffer holds the edited text) —
                // the user can retry; only the PATCH accrual is deferred to success.
                assert!(ed.is_dirty(), "the unsaved edit remains dirty for a retry");
                assert!(
                    ed.status().to_string().contains("save FAILED"),
                    "the status surfaces the refusal: {}",
                    ed.status()
                );
            });
        })
        .unwrap();
}
