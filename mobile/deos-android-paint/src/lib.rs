//! graphideOS step 2: a gpui app painting a real deos frame on android.
//!
//! This is the proof that `gpui_android` (the new `PlatformAndroid` backend in
//! the emberian/zed fork) reaches the framebuffer: a deos "first-run welcome"
//! frame — the AOL-wonder home garden's opening note — painted by gpui over the
//! `ANativeWindow` → `raw_window_handle` → wgpu/Vulkan path.
//!
//! Entry: the `android-activity` runtime calls `android_main(app)`; we hand the
//! `AndroidApp` to `gpui_android`, then run a normal gpui `Application`.

use android_activity::AndroidApp;
use gpui::{
    App, AppContext, Bounds, Context, IntoElement, ParentElement, Render, Styled, Window,
    WindowBounds, WindowOptions, div, px, rgb, size,
};
use gpui_platform::application;

/// The deos welcome frame. A dark cockpit field with a single glowing welcome
/// card — the "click a glowing card and delight" litmus, on a phone.
struct DeosWelcome;

impl Render for DeosWelcome {
    fn render(&mut self, _window: &mut Window, _cx: &mut Context<Self>) -> impl IntoElement {
        div()
            // The cockpit field.
            .size_full()
            .flex()
            .flex_col()
            .justify_center()
            .items_center()
            .gap_6()
            .bg(rgb(0x0a0e14))
            .text_color(rgb(0xe6edf3))
            .child(
                // The welcome title.
                div().text_3xl().child("welcome to deos"),
            )
            .child(
                // The glowing welcome card.
                div()
                    .flex()
                    .flex_col()
                    .gap_3()
                    .px_8()
                    .py_6()
                    .rounded_xl()
                    .bg(rgb(0x141b26))
                    .border_2()
                    .border_color(rgb(0x3b82f6))
                    .shadow_lg()
                    .child(div().text_xl().child("a turn commits."))
                    .child(div().text_xl().child("a receipt lands."))
                    .child(
                        div()
                            .text_color(rgb(0x7ee787))
                            .child("on android. painted by gpui."),
                    ),
            )
            .child(
                // The cap-badge strip (a nod to the visible-capabilities HIG).
                div()
                    .flex()
                    .gap_3()
                    .child(cap_badge(rgb(0x3b82f6)))
                    .child(cap_badge(rgb(0x7ee787)))
                    .child(cap_badge(rgb(0xf2cc60)))
                    .child(cap_badge(rgb(0xff7b72))),
            )
    }
}

fn cap_badge(color: gpui::Rgba) -> impl IntoElement {
    div()
        .size_10()
        .rounded_full()
        .bg(color)
        .border_2()
        .border_color(rgb(0x0a0e14))
}

fn run_deos() {
    application().run(|cx: &mut App| {
        // On android the platform makes the window full-screen regardless of the
        // requested bounds; we still pass a sane size for the (ignored) request.
        let bounds = Bounds::centered(None, size(px(1080.), px(2400.)), cx);
        cx.open_window(
            WindowOptions {
                window_bounds: Some(WindowBounds::Windowed(bounds)),
                ..Default::default()
            },
            |_, cx| cx.new(|_| DeosWelcome),
        )
        .expect("failed to open deos window");
        cx.activate(true);
    });
}

/// Read an android system property via `__system_property_get` (libc).
fn get_system_property(name: &str) -> Option<String> {
    use core::ffi::c_char;
    use std::ffi::CString;
    let cname = CString::new(name).ok()?;
    let mut buf = [0u8; 92]; // PROP_VALUE_MAX
    unsafe extern "C" {
        fn __system_property_get(name: *const c_char, value: *mut c_char) -> i32;
    }
    let len = unsafe { __system_property_get(cname.as_ptr(), buf.as_mut_ptr() as *mut c_char) };
    if len <= 0 {
        return None;
    }
    Some(String::from_utf8_lossy(&buf[..len as usize]).into_owned())
}

#[unsafe(no_mangle)]
fn android_main(app: AndroidApp) {
    android_logger::init_once(
        android_logger::Config::default().with_max_level(log::LevelFilter::Info),
    );
    log::info!("deos-android-paint: android_main");
    // Backend selection: read the android system property `debug.gpui.backends`
    // (set via `adb shell setprop debug.gpui.backends vulkan|gl|...`) so we can
    // iterate on the emulator's flaky GPU passthrough without rebuilding. Falls
    // back to the gpui_wgpu default (Vulkan|GL) when unset.
    if std::env::var_os("GPUI_WGPU_BACKENDS").is_none() {
        if let Some(b) = get_system_property("debug.gpui.backends") {
            if !b.is_empty() {
                unsafe { std::env::set_var("GPUI_WGPU_BACKENDS", b) };
            }
        }
    }
    gpui_android::init_logging();
    // Hand the AndroidApp to the platform BEFORE building the Application —
    // gpui_platform::application() → current_platform() reads it.
    gpui_android::set_android_app(app);
    run_deos();
}
