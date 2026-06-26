//! **The android-cell desktop window** — mount a live, cap-confined Android app as an
//! NT/Pharo desktop window whose body is the app's captured surface and whose
//! pointer/key events drive cap-gated input INTO the confined runtime.
//!
//! `servo:web :: android-runtime:android` reaches the desktop here. The webcell tab
//! routes a focused tile's typed keys + pointer events into the live Servo engine
//! (`panels_webshell.rs`); this routes the SAME desktop input into the `android-cell`
//! runtime. Clicking the window TAPS the app; typing into it types into the focused
//! field; the window body re-shows the recaptured frame.
//!
//! # Why this submodule is thin + gpui-free
//!
//! The heavy half — the `android-cell` runtime (an emulator/redroid + `adb`), the
//! `RgbaFrame` capture, and the gpui `img()` paint of the tile — lives in the
//! `native-full` build (the same place the cockpit's web-tile paint lives, and the
//! same feature-trap caveat applies). This module is the **mount wire**: the pure,
//! testable mapping the gpui window body calls — *window-pixel pointer/key event →
//! a device-space `AndroidInputCmd`* — plus the window-type descriptor. It has NO gpui
//! and NO `android-cell` dependency, so it compiles + tests in the gpui-free `--lib`
//! suite, and the gpui body simply (a) paints the captured `RgbaFrame` and (b) forwards
//! each pointer/key event through [`AndroidWindow::pointer_at`] / [`AndroidWindow::key`]
//! into the `android-cell` [`AndroidInputGate`] over the window's held cap.
//!
//! ## The exact gpui wire (named, for the `native-full` body)
//!
//! In `deos_desktop/mod.rs`, a `WinKind::AndroidCell { window: AndroidWindow, gate,
//! surface_cap, last_frame }` arm:
//! - **render:** `img(last_frame_as_image_source)` sized to the window body rect, the
//!   same `img()` paint `panels_webshell.rs` uses for the web tile.
//! - **pointer:** `.on_mouse_down(MouseButton::Left, |this, ev, _w, cx| { let cmd =
//!   win.pointer_at(ev.position - body_origin); let inp = cmd.into_android_input();
//!   let receipt = gate.deliver(&surface_cap, inp); /* recapture → last_frame */ })`.
//! - **key:** `.on_key_down(|this, ev, _w, cx| { if let Some(cmd) = win.key(&ev.keystroke)
//!   { gate.deliver(&surface_cap, cmd.into_android_input()); } })`.
//! - **repaint:** after each admitted `deliver`, call `runtime.capture_frame()` (the
//!   `AndroidInputGate::sink_mut()` hands the runtime back) → store as `last_frame` →
//!   `cx.notify()`.
//!
//! That body is ~40 lines of gpui glue over THIS module's pure logic; this is where the
//! collision-free progress lands, and the gpui arm is the one named seam left for the
//! `native-full` pass.

/// A device-space input command produced from a desktop-window event — the
/// host-independent mirror of `android_cell::AndroidInput`, kept here so this submodule
/// does not pull the heavy `android-cell` crate into the lib build. The gpui body
/// converts it to the real `AndroidInput` via [`AndroidInputCmd::as_android_tuple`] (or
/// a `From` impl behind the `native-full` feature) before handing it to the gate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AndroidInputCmd {
    /// Tap at device-pixel `(x, y)`.
    Tap { x: u32, y: u32 },
    /// Swipe (drag/scroll/fling) in device pixels over `duration_ms`.
    Swipe {
        x1: u32,
        y1: u32,
        x2: u32,
        y2: u32,
        duration_ms: u32,
    },
    /// Literal text into the focused field.
    Text { text: String },
    /// A named Android keycode (e.g. `KEYCODE_BACK`).
    Key { keycode: String },
}

impl AndroidInputCmd {
    /// A stable structural view the `native-full` body matches on to build the real
    /// `android_cell::AndroidInput` (kept as a plain tuple so this crate need not name
    /// the android-cell type). The first element is the kind tag.
    pub fn kind_tag(&self) -> &'static str {
        match self {
            AndroidInputCmd::Tap { .. } => "tap",
            AndroidInputCmd::Swipe { .. } => "swipe",
            AndroidInputCmd::Text { .. } => "text",
            AndroidInputCmd::Key { .. } => "key",
        }
    }
}

/// **The android-cell desktop window.** Holds the geometry that maps a window-pixel
/// event into the hosted app's device-pixel coordinate space — the load-bearing
/// transform that makes "clicking the window taps the app" correct under any window
/// size, scroll, or device resolution.
///
/// The window body shows the captured frame scaled to `body_w × body_h`; the device
/// surface is `device_w × device_h`. A pointer at window-body `(px, py)` therefore lands
/// on device pixel `(px * device_w / body_w, py * device_h / body_h)`.
#[derive(Clone, Debug, PartialEq)]
pub struct AndroidWindow {
    /// The captured device surface size (device pixels), from the runtime's last frame.
    pub device_w: u32,
    pub device_h: u32,
    /// The window body size the tile is painted into (logical pixels).
    pub body_w: f32,
    pub body_h: f32,
}

impl AndroidWindow {
    /// A window for a device of `device_w × device_h`, body painted at `body_w × body_h`.
    pub fn new(device_w: u32, device_h: u32, body_w: f32, body_h: f32) -> Self {
        AndroidWindow {
            device_w,
            device_h,
            body_w,
            body_h,
        }
    }

    /// **THE COORDINATE TRANSFORM.** Map a pointer at window-body `(bx, by)` (logical
    /// pixels, origin at the body top-left) to the device pixel it targets. Clamped to
    /// the device bounds (an out-of-body pointer maps to the nearest edge pixel, never a
    /// wild coordinate). Returns `None` if the window body has zero extent (degenerate).
    pub fn body_to_device(&self, bx: f32, by: f32) -> Option<(u32, u32)> {
        if self.body_w <= 0.0 || self.body_h <= 0.0 {
            return None;
        }
        let fx = (bx / self.body_w).clamp(0.0, 1.0);
        let fy = (by / self.body_h).clamp(0.0, 1.0);
        // Map into [0, device-1].
        let dx = (fx * (self.device_w.saturating_sub(1)) as f32).round() as u32;
        let dy = (fy * (self.device_h.saturating_sub(1)) as f32).round() as u32;
        Some((dx, dy))
    }

    /// **POINTER → TAP.** A click on the window body at `(bx, by)` becomes a device-space
    /// tap command the gpui body hands to the cap-gated input gate.
    pub fn pointer_at(&self, bx: f32, by: f32) -> Option<AndroidInputCmd> {
        let (x, y) = self.body_to_device(bx, by)?;
        Some(AndroidInputCmd::Tap { x, y })
    }

    /// **DRAG → SWIPE.** A press-drag-release on the body (from `(bx1,by1)` to
    /// `(bx2,by2)`) becomes a device-space swipe — scroll/fling on the hosted app.
    pub fn drag(
        &self,
        bx1: f32,
        by1: f32,
        bx2: f32,
        by2: f32,
        duration_ms: u32,
    ) -> Option<AndroidInputCmd> {
        let (x1, y1) = self.body_to_device(bx1, by1)?;
        let (x2, y2) = self.body_to_device(bx2, by2)?;
        Some(AndroidInputCmd::Swipe {
            x1,
            y1,
            x2,
            y2,
            duration_ms,
        })
    }

    /// **KEY → AndroidInput.** Map a desktop keystroke to a device input command. A
    /// single printable character is sent as literal text; the common navigation/edit
    /// keys map to their Android keycodes (the same mapping a webshell tile uses to feed
    /// the engine). An unmapped chord returns `None` (swallowed, never an ambient key).
    pub fn key(&self, key: &str) -> Option<AndroidInputCmd> {
        // Named keys first.
        let keycode = match key {
            "backspace" | "delete" => Some("KEYCODE_DEL"),
            "enter" | "return" => Some("KEYCODE_ENTER"),
            "tab" => Some("KEYCODE_TAB"),
            "escape" => Some("KEYCODE_ESCAPE"),
            "left" => Some("KEYCODE_DPAD_LEFT"),
            "right" => Some("KEYCODE_DPAD_RIGHT"),
            "up" => Some("KEYCODE_DPAD_UP"),
            "down" => Some("KEYCODE_DPAD_DOWN"),
            "home" => Some("KEYCODE_HOME"),
            "space" => Some("KEYCODE_SPACE"),
            _ => None,
        };
        if let Some(kc) = keycode {
            return Some(AndroidInputCmd::Key {
                keycode: kc.to_string(),
            });
        }
        // A single printable character → literal text into the focused field.
        let mut chars = key.chars();
        match (chars.next(), chars.next()) {
            (Some(c), None) if !c.is_control() => Some(AndroidInputCmd::Text {
                text: c.to_string(),
            }),
            _ => None,
        }
    }
}

/// The desktop window-type descriptor for an android-cell — the small const surface the
/// desktop chrome (title bar, menu, persistence tag) reads. Mirrors how the other
/// `WinKind`s carry a `label()`; defined here so the descriptor lives with the window.
pub const ANDROID_WINDOW_TITLE: &str = "Android Cell";

#[cfg(test)]
mod tests {
    use super::*;

    /// **THE LOAD-BEARING TRANSFORM TEST.** A click in the CENTER of the window body
    /// taps the CENTER of the device, regardless of the body/device size mismatch — the
    /// mapping that makes "clicking the window taps the app" correct.
    #[test]
    fn center_click_taps_device_center() {
        // A 1080×2400 device shown in a 360×800 window body (3× downscale).
        let w = AndroidWindow::new(1080, 2400, 360.0, 800.0);
        let cmd = w.pointer_at(180.0, 400.0).expect("center maps");
        match cmd {
            AndroidInputCmd::Tap { x, y } => {
                // Center of the body → center of the device (±1 for rounding).
                assert!((x as i64 - 539).abs() <= 1, "x≈center, got {x}");
                assert!((y as i64 - 1199).abs() <= 1, "y≈center, got {y}");
            }
            other => panic!("expected a tap, got {other:?}"),
        }
    }

    /// A corner click maps to the corner device pixel; an out-of-body click clamps to
    /// the nearest edge (never a wild coordinate that could miss the surface).
    #[test]
    fn corners_and_clamping() {
        let w = AndroidWindow::new(1080, 2400, 360.0, 800.0);
        assert_eq!(w.body_to_device(0.0, 0.0), Some((0, 0)));
        assert_eq!(w.body_to_device(360.0, 800.0), Some((1079, 2399)));
        // Out of body → clamped to the far edge, not extrapolated.
        assert_eq!(w.body_to_device(99999.0, 99999.0), Some((1079, 2399)));
        assert_eq!(w.body_to_device(-50.0, -50.0), Some((0, 0)));
    }

    #[test]
    fn drag_becomes_a_device_swipe() {
        let w = AndroidWindow::new(1080, 2400, 360.0, 800.0);
        let cmd = w
            .drag(180.0, 600.0, 180.0, 200.0, 250)
            .expect("a drag maps to a swipe");
        match cmd {
            AndroidInputCmd::Swipe {
                x1,
                y1,
                x2,
                y2,
                duration_ms,
            } => {
                assert!((x1 as i64 - 539).abs() <= 1);
                assert!((x2 as i64 - 539).abs() <= 1);
                assert!(y1 > y2, "a downward drag in body → upward swipe (scroll)");
                assert_eq!(duration_ms, 250);
            }
            other => panic!("expected a swipe, got {other:?}"),
        }
    }

    #[test]
    fn key_mapping_named_and_printable() {
        let w = AndroidWindow::new(1080, 2400, 360.0, 800.0);
        assert_eq!(
            w.key("enter"),
            Some(AndroidInputCmd::Key {
                keycode: "KEYCODE_ENTER".into()
            })
        );
        assert_eq!(
            w.key("backspace"),
            Some(AndroidInputCmd::Key {
                keycode: "KEYCODE_DEL".into()
            })
        );
        // A single printable char → text.
        assert_eq!(w.key("a"), Some(AndroidInputCmd::Text { text: "a".into() }));
        // An unmapped chord is swallowed (no ambient key reaches the app).
        assert_eq!(w.key("cmd-shift-p"), None);
    }

    #[test]
    fn degenerate_window_maps_nothing() {
        let w = AndroidWindow::new(1080, 2400, 0.0, 0.0);
        assert_eq!(w.pointer_at(1.0, 1.0), None);
    }
}
