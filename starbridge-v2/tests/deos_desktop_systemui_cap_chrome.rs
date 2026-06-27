//! **THE GRAPHIDEOS SYSTEMUI CAP-CHROME ON THE GLASS.**
//!
//! The deos desktop renders a confined android-cell's permission UI AS the phone's
//! SystemUI — the proven `systemui_caps::SystemUiCapChrome` model painted into a real
//! `WinKind::AndroidCell` window. This bake opens that window in a HEADLESS desktop (so
//! the gpui body actually PAINTS — a render panic would fail the test) and drives the
//! three SystemUI surfaces over the live confined cap-chrome:
//!
//!   * the **status-bar strip** shows the held authorities at a glance (INTERNET lit at
//!     install; the dangerous caps dim until handed over);
//!   * the **quick-settings shade** pulls down the WHOLE roster (no hidden Settings tree);
//!   * tapping a **hand-over row** drives a REAL `Effect::GrantCapability` through the
//!     verified executor — LOCATION lands (the badge flips lit because the cell GENUINELY
//!     holds it), and CAMERA (which the device principal cannot back) is REFUSED by the
//!     executor itself, the cap never landing (the powerbox tooth, no ambient escalation).
//!
//! Run: `cd starbridge-v2 && cargo test --no-default-features \
//!   --features "gpui-ui,embedded-executor,android-systemui,render-capture" \
//!   --test deos_desktop_systemui_cap_chrome -- --nocapture`

#![cfg(all(
    feature = "gpui-ui",
    feature = "embedded-executor",
    feature = "android-systemui"
))]

use std::borrow::Cow;
use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;

use gpui::{px, size, AppContext, HeadlessAppContext, PlatformTextSystem};
use gpui_wgpu::CosmicTextSystem;

use android_cell::AndroidPermission;
use starbridge_v2::deos_desktop::DeosDesktop;
use starbridge_v2::world::demo_world;

static LILEX: &[u8] = include_bytes!("../assets/fonts/Lilex-Regular.ttf");
static IBM_PLEX: &[u8] = include_bytes!("../assets/fonts/IBMPlexSans-Regular.ttf");

#[test]
fn the_desktop_renders_a_confined_android_cells_systemui_cap_chrome() {
    let layout_path =
        std::env::temp_dir().join(format!("deos-sysui-test-{}.json", std::process::id()));
    let _ = std::fs::remove_file(&layout_path);

    let (world, anchors) = demo_world();
    let [_treasury, _service, user] = anchors;
    let shared = Rc::new(RefCell::new(world));

    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system
        .add_fonts(vec![Cow::Borrowed(LILEX), Cow::Borrowed(IBM_PLEX)])
        .expect("fonts");
    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(gpui_component::init);

    let world_for_view = shared.clone();
    let lp = layout_path.clone();
    let desk_cell: Rc<RefCell<Option<gpui::Entity<DeosDesktop>>>> = Rc::new(RefCell::new(None));
    let desk_sink = desk_cell.clone();
    let window = cx
        .open_window(size(px(900.), px(640.)), move |window, cx| {
            let view = cx.new(|cx| DeosDesktop::new(world_for_view, user, lp, window, cx));
            *desk_sink.borrow_mut() = Some(view.clone());
            cx.new(|cx| gpui_component::Root::new(gpui::AnyView::from(view), window, cx))
        })
        .expect("open the headless desktop window");
    cx.run_until_parked();
    let desk = desk_cell.borrow().clone().expect("desktop entity captured");

    // Force a real repaint of the headless window (the first frame painted on open;
    // a later state change needs `refresh()` to repaint). After this the AndroidCell
    // window's body PAINTS through the gpui render — a render panic would fail here.
    let paint = |cx: &mut gpui::HeadlessAppContext| {
        cx.update_window(window.into(), |_, w, _| w.refresh())
            .expect("refresh the headless window");
        cx.run_until_parked();
    };

    // Open the android-cell window — its body is the SystemUI cap-chrome. The first
    // paint MINTS the confined chrome (its real PermWorld + executor) and renders it.
    // (Dismiss the one-time Welcome card so the window is on the bare glass.)
    desk.update(&mut cx, |d, _cx| {
        d.bake_dismiss_welcome();
        d.bake_open_android_cell(user);
    });
    paint(&mut cx);

    // ── The status-bar strip: INTERNET lit at install; the dangerous caps dim. ──
    let held = cx.update(|cx| desk.read(cx).clone_status_held(user));
    assert!(
        held.iter().any(|h| h.contains("NET")),
        "the status bar lights INTERNET at install: {held:?}"
    );
    assert!(
        !held.iter().any(|h| h.contains("LOCATION")),
        "LOCATION is dim until handed over: {held:?}"
    );

    // ── The quick-settings shade: the WHOLE roster, lit ●/dim ○, nothing hidden. ──
    desk.update(&mut cx, |d, _cx| d.bake_android_toggle_shade(user));
    paint(&mut cx); // the shade paints (the gpui render runs again)
    let roster = cx.update(|cx| desk.read(cx).clone_quick_settings(user));
    assert!(
        roster.iter().any(|l| l.contains("● NET")),
        "the shade shows INTERNET lit: {roster:?}"
    );
    assert!(
        roster.iter().any(|l| l.contains("○ LOCATION")),
        "the shade shows LOCATION dim with its reason: {roster:?}"
    );
    let sheet_before = cx.update(|cx| desk.read(cx).clone_sheet_len(user));
    assert!(
        sheet_before >= 2,
        "the hand-over sheet lists the declared dim dangerous caps (LOCATION + CAMERA): {sheet_before}"
    );

    // ── THE KEYSTONE: tap LOCATION → a REAL kernel grant; the badge flips lit. ──
    let granted = desk.update(&mut cx, |d, _cx| {
        d.bake_android_hand_over(user, AndroidPermission::AccessFineLocation)
    });
    paint(&mut cx);
    assert!(
        granted,
        "the device principal can back LOCATION → it hands over"
    );
    let held_after = cx.update(|cx| desk.read(cx).clone_status_held(user));
    assert!(
        held_after.iter().any(|h| h.contains("LOCATION")),
        "after the hand-over the status bar lights LOCATION (the cell GENUINELY holds it): {held_after:?}"
    );

    // ── THE POWERBOX TOOTH: tap CAMERA → REFUSED by the executor; the cap never lands. ──
    let camera = desk.update(&mut cx, |d, _cx| {
        d.bake_android_hand_over(user, AndroidPermission::Camera)
    });
    paint(&mut cx);
    assert!(
        !camera,
        "the device principal holds NO camera authority → the executor refuses (no ambient escalation)"
    );
    let held_final = cx.update(|cx| desk.read(cx).clone_status_held(user));
    assert!(
        !held_final.iter().any(|h| h.contains("CAMERA")),
        "CAMERA stays dim — a refused hand-over lands nothing: {held_final:?}"
    );

    // Capture the painted glass — a real PNG of the SystemUI cap-chrome window (status
    // bar with NET + LOCATION lit, the pulled-down shade, the CAMERA hand-over row).
    #[cfg(feature = "render-capture")]
    {
        paint(&mut cx);
        if let Ok(img) = cx.capture_screenshot(window.into()) {
            let out = std::env::temp_dir().join("deos-systemui-cap-chrome-on-the-glass.png");
            let _ = img.save(&out);
            println!("PNG: {} ({}x{})", out.display(), img.width(), img.height());
        }
    }

    let _ = std::fs::remove_file(&layout_path);
    println!(
        "OK the desktop renders a confined android-cell's SystemUI cap-chrome: status bar lit \
         {held:?} → after a REAL LOCATION hand-over {held_after:?}; the shade shows the whole \
         roster ({} rows); CAMERA refused by the executor (no ambient escalation).",
        roster.len()
    );
}
