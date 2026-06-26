//! THE STRUCTURE-PANE seam: the cockpit editor surface can show, live, the
//! document's STRUCTURE — its blame timeline + first-class conflict objects — of
//! the SAME document open in the buffer, toggled in place.
//!
//! Where `firmament_pane.rs` proves a save is a receipted turn through the pane,
//! this proves the OTHER half of the dregg-doc weld is reachable from the running
//! cockpit pane (not just the `merge_demo` bin): the `EditorPaneView`'s
//! buffer⇄structure toggle drives a `DocViewer` whose snapshot tracks the editor's
//! live `RopeDoc`. Drives the REAL gpui `EditorSurface` in a headless gpui app.
//!
//! Run with:
//!   cargo test --features "firmament screenshot" --test editor_structure_pane

#![cfg(all(
    feature = "firmament",
    feature = "cockpit-surface",
    feature = "screenshot"
))]

use std::borrow::Cow;
use std::path::PathBuf;
use std::sync::Arc;

use gpui::{
    AppContext as _, HeadlessAppContext, IntoElement, PlatformTextSystem, Render, px, size,
};
use gpui_wgpu::CosmicTextSystem;

use deos_zed::cockpit_surface::{EditorSurface, ViewMode};

static LILEX: &[u8] = include_bytes!("../assets/fonts/Lilex-Regular.ttf");
static IBM_PLEX: &[u8] = include_bytes!("../assets/fonts/IBMPlexSans-Regular.ttf");

struct PaneHolder {
    surface: EditorSurface,
}

impl Render for PaneHolder {
    fn render(
        &mut self,
        window: &mut gpui::Window,
        cx: &mut gpui::Context<Self>,
    ) -> impl IntoElement {
        self.surface.render_body(window, cx)
    }
}

#[test]
fn editor_pane_structure_toggle_tracks_the_live_document() {
    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system
        .add_fonts(vec![Cow::Borrowed(LILEX), Cow::Borrowed(IBM_PLEX)])
        .expect("load fonts");

    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(|cx| gpui_component::init(cx));

    let path = "/deos/main.rs";
    let seed = "fn main() {\n    println!(\"before\");\n}\n";
    let edited = "fn main() {\n    println!(\"AFTER — a second patch\");\n}\n";

    let window = cx
        .open_window(size(px(900.), px(600.)), |window, cx| {
            cx.new(|cx| {
                let surface = EditorSurface::firmament(
                    7,
                    PathBuf::from("/deos"),
                    &[(path, seed)],
                    window,
                    cx,
                )
                .expect("firmament surface mounts");
                PaneHolder { surface }
            })
        })
        .expect("headless window");

    cx.run_until_parked();

    // 1. The pane starts on the editable BUFFER face, and its structure inspector
    //    is already snapshotted from the opened document (one genesis patch, blame
    //    for the open content) — the toggle will surface it.
    window
        .update(&mut cx, |holder, _window, cx| {
            let surface = &holder.surface;
            assert_eq!(surface.mode(cx), ViewMode::Buffer, "starts on the buffer");
            let dv = surface.view().read(cx).doc_viewer().read(cx);
            assert_eq!(
                dv.patch_count(),
                1,
                "the opened document has its genesis patch"
            );
            assert!(
                dv.blame_len() > 0,
                "blame is snapshotted for the open content"
            );
            assert!(
                !dv.has_conflict(),
                "a freshly-opened single-author doc is clean"
            );
        })
        .unwrap();

    // 2. Toggle to the STRUCTURE face — the host path the toggle click drives.
    window
        .update(&mut cx, |holder, _window, cx| {
            holder.surface.set_mode(ViewMode::Structure, cx);
        })
        .unwrap();
    cx.run_until_parked();

    window
        .update(&mut cx, |holder, _window, cx| {
            assert_eq!(
                holder.surface.mode(cx),
                ViewMode::Structure,
                "the toggle switched the shown face"
            );
        })
        .unwrap();

    // 3. Edit + save through the editor (a second patch), then re-enter Structure so
    //    the inspector re-snapshots — the structure tracks the LIVE document.
    window
        .update(&mut cx, |holder, window, cx| {
            let editor = holder.surface.editor().clone();
            editor.update(cx, |ed, cx| {
                ed.set_text(edited, window, cx);
                ed.save(cx).expect("save commits a turn");
            });
            // back to Buffer then Structure to force a refresh from the live doc.
            holder.surface.set_mode(ViewMode::Buffer, cx);
            holder.surface.set_mode(ViewMode::Structure, cx);
        })
        .unwrap();
    cx.run_until_parked();

    window
        .update(&mut cx, |holder, _window, cx| {
            let dv = holder.surface.view().read(cx).doc_viewer().read(cx);
            assert!(
                dv.patch_count() >= 2,
                "the save accrued a second patch the structure inspector now reflects: {}",
                dv.patch_count()
            );
            assert!(
                dv.segment_count() > 0,
                "the inspector renders the document's structure"
            );
            assert!(
                !dv.has_conflict(),
                "a single-author edit/save chain stays clean — no conflict yet"
            );
        })
        .unwrap();

    // 4. THE MERGE/CONFLICT ACTION — the gap-closer. A single-author session
    //    cannot, by typing alone, produce a conflict; the pane's merge action
    //    forks two divergent co-author takes of the open document and merges them
    //    (the real pushout), surfacing a FIRST-CLASS conflict object the structure
    //    pane shows. This is the button click's host path.
    window
        .update(&mut cx, |holder, window, cx| {
            holder.surface.view().update(cx, |v, cx| {
                v.merge_coauthor_take(window, cx);
            });
        })
        .unwrap();
    cx.run_until_parked();

    window
        .update(&mut cx, |holder, _window, cx| {
            assert_eq!(
                holder.surface.mode(cx),
                ViewMode::Structure,
                "the merge action surfaces the conflict in the structure face"
            );
            let dv = holder.surface.view().read(cx).doc_viewer().read(cx);
            assert!(
                dv.has_conflict(),
                "the co-author merge produced a first-class conflict object in-session"
            );
        })
        .unwrap();
}
