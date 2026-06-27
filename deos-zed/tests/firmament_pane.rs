//! THE THROUGH-THE-PANE firmament test: the cockpit editor surface, built
//! firmament-backed, opens a seeded file-cell THROUGH the editor's own
//! `open()`, a host-driven edit + `save()` fires a REAL cap-gated turn, and the
//! genuine `TurnReceipt` lands on the in-process ledger.
//!
//! This is the honest discipline the seam owes: not the gpui-free `Fs`-trait
//! test (that already exists in `firmament_fs.rs`), but the SAME path the
//! running pane uses — a real gpui `Editor` entity in a headless gpui app,
//! constructed by `EditorSurface::firmament` (exactly what `starbridge-v2`'s
//! `EditorPane::new` calls under the `firmament` feature), opened + edited +
//! saved through the editor entity.
//!
//! Gated on `firmament` (the live FS) + `cockpit-surface` (the surface) +
//! `screenshot` (the headless gpui harness — `HeadlessAppContext` + offscreen
//! renderer + no-system-fonts text). Run with:
//!   cargo test --features "firmament screenshot" --test firmament_pane

#![cfg(all(
    feature = "firmament",
    feature = "cockpit-surface",
    feature = "screenshot"
))]

use std::borrow::Cow;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use gpui::{
    px, size, AppContext as _, HeadlessAppContext, IntoElement, PlatformTextSystem, Render,
};
use gpui_wgpu::CosmicTextSystem;

use std::rc::Rc;

use deos_zed::cockpit_surface::EditorSurface;
use deos_zed::fs::{FirmamentFs, Fs, LedgerSpine, OwnedSpine};

// The same OFL fonts the screenshot harness ships, so text shaping is real and
// deterministic with no system fonts.
static LILEX: &[u8] = include_bytes!("../assets/fonts/Lilex-Regular.ttf");
static IBM_PLEX: &[u8] = include_bytes!("../assets/fonts/IBMPlexSans-Regular.ttf");

/// A trivial gpui root view holding the surface so we can drive it through the
/// window's typed entity handle (the surface itself isn't a `Render` root).
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
fn cockpit_editor_pane_save_is_a_receipted_turn_through_the_pane() {
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
    let edited = "fn main() {\n    println!(\"AFTER — a receipted turn\");\n}\n";

    // Build the FIRMAMENT-backed surface — the exact constructor
    // `EditorPane::new` routes to under the `firmament` feature. The first
    // seeded file is opened THROUGH the editor's `open()` in the constructor.
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

    // 1. The buffer opened onto the CELL content (open() read the cell, not disk),
    //    and no save has run yet.
    window
        .update(&mut cx, |holder, _window, cx| {
            let buf = holder.surface.editor().read(cx).text(cx);
            assert_eq!(buf, seed, "the pane opened onto the seeded cell content");
            assert_eq!(
                holder.surface.receipt_count(),
                Some(0),
                "no saves yet — a seed is genesis, not a turn"
            );
        })
        .unwrap();

    // 2. Drive a host edit + save THROUGH the editor entity (the running pane's
    //    own path: set the buffer, then `save()` -> `fs.save` -> a real turn).
    window
        .update(&mut cx, |holder, window, cx| {
            let editor = holder.surface.editor().clone();
            editor.update(cx, |ed, cx| {
                ed.set_text(edited, window, cx);
                ed.save(cx).expect("save commits a turn");
            });
        })
        .unwrap();

    cx.run_until_parked();

    // 3. A REAL receipt landed on the ledger; the cell content updated.
    window
        .update(&mut cx, |holder, _window, cx| {
            let surface = &holder.surface;

            assert_eq!(
                surface.receipt_count(),
                Some(1),
                "the save produced ONE receipt"
            );
            let firm: &Arc<FirmamentFs> = surface.firmament_fs().expect("firmament-backed");
            let receipt = firm.last_receipt().expect("a receipt was recorded");
            assert_eq!(
                receipt.agent,
                firm.editor_id(),
                "the editor cell is the turn's agent"
            );
            assert_ne!(
                receipt.pre_state_hash, receipt.post_state_hash,
                "the edit moved the ledger state (the save landed on-ledger)"
            );

            // The cell now holds the edited content, read back FROM THE LEDGER
            // through the same Fs handle the pane uses.
            let on_ledger = firm.load(Path::new(path)).expect("load the cell");
            assert_eq!(
                on_ledger, edited,
                "the edited content round-trips through the ledger, not disk"
            );

            // The editor's buffer matches, and the status reflects the REAL
            // on-ledger save (not a disk write / patch-history count).
            let buf = surface.editor().read(cx).text(cx);
            assert_eq!(buf, edited);
            let status = surface.editor().read(cx).status().to_string();
            assert!(
                status.contains("on-ledger"),
                "the status line reflects the real on-ledger save: {status}"
            );
        })
        .unwrap();
}

/// THE SHARED-LEDGER SEAM test: the editor pane edits the SAME ledger a second
/// reader inspects — exactly the cockpit's `World`-shared mount, modeled here
/// with a shared [`OwnedSpine`].
///
/// The cockpit owns its verified spine (`Rc<RefCell<World>>`) and its cell
/// inspector reads `World::ledger()`. The editor pane, when mounted
/// `FirmamentFs::over` that spine, must land its saves on THAT SAME ledger — so a
/// second reader of the spine (the inspector) sees the save as a new receipt + a
/// new cell content, not a per-editor copy. Here:
///   * `spine: Rc<OwnedSpine>` is the shared verified spine (stands in for the
///     cockpit's live `World`),
///   * the editor pane is `FirmamentFs::over(spine.clone())` — the pane the
///     `firmament_over` constructor builds,
///   * `inspector: Rc<dyn LedgerSpine>` is a SECOND handle on the SAME spine
///     (stands in for the cockpit's cell inspector),
///
/// and after the editor drives a real `save()`, the inspector — NOT the editor's
/// fs — is asserted to see the new receipt + the edited cell content.
#[test]
fn editor_pane_save_lands_on_the_shared_ledger_a_second_reader_inspects() {
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
    let edited = "fn main() {\n    println!(\"AFTER — landed on the SHARED ledger\");\n}\n";

    // THE SHARED VERIFIED SPINE — one ledger + executor, exactly as the cockpit
    // owns ONE `World`. Two handles on it: one the editor's fs mounts over, one
    // the "inspector" reads.
    let spine: Rc<OwnedSpine> = Rc::new(OwnedSpine::new());
    let inspector: Rc<dyn LedgerSpine> = spine.clone();

    // The editor's fs mounts OVER the shared spine (NOT a fresh one). This is the
    // `FirmamentFs::over` the cockpit's `firmament_over` builds. The seed is
    // installed by `firmament_over` itself (once) onto the SHARED ledger — we do
    // NOT pre-seed, so there is exactly ONE file cell at `path`.
    // Typed `Arc<FirmamentFs>` (the `firmament_over` param shape); single-threaded
    // test, so the !Send/!Sync Arc is intentional.
    #[allow(clippy::arc_with_non_send_sync)]
    let firm: Arc<FirmamentFs> = Arc::new(FirmamentFs::over(spine.clone()));

    assert_eq!(
        inspector.receipt_count(),
        0,
        "no saves yet on the shared ledger"
    );
    let balance_before_seed = inspector.total_balance();

    // Build the editor surface over the shared-spine fs — the EXACT pane shape
    // `EditorSurface::firmament_over` builds, driven through the real gpui editor.
    // It seeds `(path, seed)` onto the shared ledger and opens it in the buffer.
    let window = cx
        .open_window(size(px(900.), px(600.)), |window, cx| {
            cx.new(|cx| {
                let surface = EditorSurface::firmament_over(
                    11,
                    firm.clone(),
                    PathBuf::from("/deos"),
                    &[(path, seed)],
                    window,
                    cx,
                )
                .expect("firmament_over surface mounts");
                PaneHolder { surface }
            })
        })
        .expect("headless window");

    cx.run_until_parked();

    // Learn the file cell the (single) seed installed on the shared ledger, and
    // confirm the inspector reads its genesis content off that SAME ledger.
    let file = firm
        .cell_for(Path::new(path))
        .expect("the seed installed a file cell");
    {
        let cell = inspector
            .cell(&file)
            .expect("the seeded cell is on the shared ledger");
        let content = deos_zed::fs::host_decode_content(&cell).expect("decode");
        assert_eq!(content, seed, "the inspector reads the genesis content");
    }
    // Σ balance after the genesis seed — the baseline a content save must conserve.
    let balance_before = inspector.total_balance();
    let _ = balance_before_seed;

    // Drive a host edit + save THROUGH the editor entity (the running pane path).
    window
        .update(&mut cx, |holder, window, cx| {
            let editor = holder.surface.editor().clone();
            editor.update(cx, |ed, cx| {
                ed.set_text(edited, window, cx);
                ed.save(cx)
                    .expect("save commits a turn on the shared ledger");
            });
        })
        .unwrap();

    cx.run_until_parked();

    // THE ASSERTION THAT CLOSES THE SEAM: the SECOND reader of the SAME ledger
    // (the inspector handle, NOT the editor's fs) sees the save — a new receipt
    // AND the edited cell content. The editor edited the ledger the inspector
    // inspects; one ledger, one save path.
    assert_eq!(
        inspector.receipt_count(),
        1,
        "the inspector sees the save as a new on-ledger receipt"
    );
    let receipt = inspector
        .last_receipt()
        .expect("the inspector sees the receipt");
    assert_eq!(
        receipt.agent,
        inspector.editor_id(),
        "the editor cell is the agent"
    );
    assert_ne!(
        receipt.pre_state_hash, receipt.post_state_hash,
        "the save moved the shared ledger's state"
    );

    let cell = inspector
        .cell(&file)
        .expect("the file cell is on the shared ledger");
    let content = deos_zed::fs::host_decode_content(&cell).expect("decode the cell");
    assert_eq!(
        content, edited,
        "the inspector reads the EDITED content off the SAME ledger the editor saved to"
    );

    // Conservation (Σδ=0): a content SetField touches no balance substance.
    assert_eq!(
        inspector.total_balance(),
        balance_before,
        "the save conserves value on the shared ledger (Σδ=0)"
    );
}
