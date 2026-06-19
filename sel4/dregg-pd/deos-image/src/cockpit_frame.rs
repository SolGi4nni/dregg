//! THE STARBRIDGE-V2 COCKPIT MODE — the REAL, LIVE starbridge-v2 cockpit,
//! rendered headless and blitted onto the seL4 framebuffer.
//!
//! `cockpit_frame.rgba` is an 800x600 RGBA8 image of the **live
//! `starbridge_v2::cockpit::Cockpit` element tree** over the fully-seeded demo
//! image (`world::demo_world` — every verified executor turn run): the CELL
//! WORLD rail with the real sovereign cells (ids, balances, cap counts, the
//! issuer well at −supply), the INSPECTOR reflecting the image (cells / height /
//! receipts / state_root / "executor embedded verified (TurnExecutor)"), the
//! BLOCKLACE provenance (the real receipt chain), and the HOME/SHELL/AGENT
//! workspace — all the actual cockpit, not a facsimile.
//!
//! It is produced by `starbridge-v2 --render-cockpit` (src/main.rs,
//! `render_cockpit_headless`): a headless gpui `App`/`Window`
//! (`gpui::HeadlessAppContext` over `TestPlatform`) drives the real `Cockpit`,
//! and its resolved gpui `Scene` is rendered offscreen by the ACTUAL gpui wgpu
//! renderer (`gpui_wgpu::WgpuHeadlessRenderer` / `render_scene_to_image`, the
//! offscreen patch — docs/desktop-os-research/GPUI-OFFSCREEN-FORK.md) on software
//! Vulkan (lavapipe/llvmpipe — NO GPU, NO window) on persvati. gpui reports a 2x
//! scale, so the 800x600-logical cockpit renders at 1600x1200 device px and is
//! Lanczos-downscaled to the framebuffer's 800x600. Same renderer leaf the
//! windowed cockpit uses (`gpui -> gpui_platform -> gpui_linux -> gpui_wgpu`).
//!
//! It is baked in EXACTLY as `image_data.rs` bakes real cells: a `#![no_std]`
//! PD cannot link wgpu/lavapipe, so the heavy render happens at build time on
//! persvati and the resulting RGBA is embedded. This module converts that RGBA
//! to the framebuffer's XRGB8888 at blit time and writes it straight into the
//! mapped framebuffer the QEMU ramfb engine scans out.
//!
//! Regenerate (the bytes, from persvati where lavapipe lives):
//!   ssh persvati '... cd starbridge-v2 && \
//!     ZED_OFFSCREEN_PREFER_CPU=1 VK_ICD_FILENAMES=…/lvp_icd.json \
//!     cargo run --release --features headless-render -- --render-cockpit OUT'
//!   scp persvati:OUT.rgba sel4/dregg-pd/deos-image/src/cockpit_frame.rgba

use crate::fb::{Canvas, HEIGHT, WIDTH};

/// The baked cockpit frame: 800x600 RGBA8, row-major, top row first, no padding
/// (w*h*4 = 1_920_000 bytes). Rendered by gpui on lavapipe — see the module doc.
pub static COCKPIT_RGBA: &[u8] = include_bytes!("cockpit_frame.rgba");

// ───────────────────────── the cockpit focus tabs ───────────────────────────
//
// The baked frame is a STATIC gpui render, so we cannot re-flow its element
// tree in the PD (no wgpu in `#![no_std]`). What we CAN do — and do here — is
// drive a REAL focus cursor OVER the frame: the keyboard's `Nav` moves a
// highlight between the cockpit's top workspace tabs (HOME / SHELL / AGENT) and
// ENTER selects one. The cursor is an overlay the `blit` repaints, so a
// keypress in cockpit mode now visibly moves the highlight on glass — the same
// IRQ -> drain -> apply -> repaint loop the image mode uses, now closed for the
// cockpit too. (The honest next rung — having the SELECTED tab actually re-flow
// the cockpit's workspace pane — needs the live off-VM re-render path; see the
// module doc + main.rs's cockpit-focus state.)
//
// Boxes measured against `cockpit-render-800x600-LIVE.png`'s top tab band: the
// three named workspace tabs sit at y≈14..28 in the top-right header.

/// One focusable tab's on-frame label box `(x, y, w, h)`. The name lives in
/// [`TABS`] at the same index (the focus order arrows walk).
struct Tab {
    x: u32,
    y: u32,
    w: u32,
    h: u32,
}

/// The cockpit's top workspace tabs, left→right (the focus order arrows walk).
pub const TABS: [&str; 3] = ["HOME", "SHELL", "AGENT"];

const TAB_BOXES: [Tab; 3] = [
    Tab { x: 602, y: 13, w: 40, h: 17 },
    Tab { x: 651, y: 13, w: 46, h: 17 },
    Tab { x: 707, y: 13, w: 44, h: 17 },
];

/// The render geometry — must equal the framebuffer geometry so the blit is a
/// straight copy. (The persvati harness renders at exactly `fb::{WIDTH,HEIGHT}`.)
pub const COCKPIT_W: u32 = 800;
pub const COCKPIT_H: u32 = 600;

const _: () = assert!(COCKPIT_W == WIDTH && COCKPIT_H == HEIGHT);

/// Blit the baked gpui cockpit frame into the framebuffer, then draw the live
/// focus cursor over it. `focus` is the index (into [`TABS`]) the keyboard is
/// hovering; `selected` is the tab last chosen with ENTER (if any). Because the
/// cursor is repainted by this same `blit`, a `Nav` keypress in cockpit mode now
/// visibly moves the highlight — the IRQ→drain→apply→repaint loop, closed for
/// the cockpit.
pub fn blit(c: &mut Canvas, focus: usize, selected: Option<usize>) {
    blit_frame(c);
    draw_focus(c, focus, selected);
}

/// Blit just the baked gpui cockpit frame into the framebuffer the QEMU ramfb
/// engine scans out, converting RGBA8 -> XRGB8888 (`0x00RRGGBB`) per pixel. A
/// real gpui render, on glass, on seL4.
fn blit_frame(c: &mut Canvas) {
    // Defensive: if the baked frame is the wrong length (a regenerate mismatch),
    // paint a solid backdrop so the mode is still visibly distinct rather than
    // reading garbage. (The const assert above already guards geometry; this
    // guards the byte length of the embedded asset.)
    let want = (COCKPIT_W * COCKPIT_H * 4) as usize;
    if COCKPIT_RGBA.len() != want {
        c.rect(0, 0, WIDTH, HEIGHT, crate::fb::rgb(11, 15, 26));
        let _ = c.text(
            "cockpit_frame.rgba length mismatch -- regenerate from persvati",
            24,
            24,
            1,
            1,
            crate::fb::rgb(232, 96, 96),
        );
        return;
    }

    for y in 0..HEIGHT {
        for x in 0..WIDTH {
            let i = ((y * WIDTH + x) * 4) as usize;
            let r = COCKPIT_RGBA[i];
            let g = COCKPIT_RGBA[i + 1];
            let b = COCKPIT_RGBA[i + 2];
            // alpha (byte i+3) ignored: the framebuffer is XRGB (opaque); the
            // cockpit backdrop is itself opaque so this is exact.
            c.put(x, y, crate::fb::rgb(r, g, b));
        }
    }

    // A thin footer hint so the mode is self-describing (LEFT/RIGHT move the tab
    // focus, ENTER selects, TAB returns to the live image). Drawn OVER the
    // blitted frame's status-bar band.
    let by = HEIGHT - 22;
    let teal = crate::fb::rgb(64, 224, 208);
    let grey = crate::fb::rgb(150, 178, 188);
    let mut x = c.text("LEFT/RIGHT", 24, by, 1, 1, teal);
    x = c.text(" focus a tab  ·  ", x, by, 1, 1, grey);
    x = c.text("ENTER", x, by, 1, 1, teal);
    x = c.text(" select  ·  ", x, by, 1, 1, grey);
    x = c.text("TAB", x, by, 1, 1, teal);
    let _ = c.text(" back to the live image", x, by, 1, 1, grey);
}

/// Draw the live focus cursor over the baked frame: an outline around the tab
/// the keyboard is hovering, and a filled underline + label under the selected
/// tab (the one chosen with ENTER). This is the cockpit mode's REAL consumption
/// of the decoded `Nav` events — a keypress moves this highlight on glass.
fn draw_focus(c: &mut Canvas, focus: usize, selected: Option<usize>) {
    let teal = crate::fb::rgb(64, 224, 208);
    let amber = crate::fb::rgb(255, 196, 92);

    // The hovered tab: a 2px teal outline, clamped into [0, TABS.len()).
    let f = focus.min(TAB_BOXES.len() - 1);
    let t = &TAB_BOXES[f];
    c.frame(t.x, t.y, t.w, t.h, 2, teal);

    // The selected tab: an amber underline directly under its label.
    if let Some(s) = selected {
        if let Some(t) = TAB_BOXES.get(s) {
            c.rect(t.x, t.y + t.h + 1, t.w, 2, amber);
        }
    }

    // A small status line just under the tab band, naming the focused/selected
    // tab, so the consumption is legible even on a still screenshot.
    let sy = TAB_BOXES[0].y + TAB_BOXES[0].h + 6;
    let mut x = c.text("focus ", 560, sy, 1, 1, crate::fb::rgb(150, 178, 188));
    x = c.text(TABS[f], x, sy, 1, 1, teal);
    if let Some(s) = selected {
        if let Some(name) = TABS.get(s) {
            x = c.text("  sel ", x, sy, 1, 1, crate::fb::rgb(150, 178, 188));
            let _ = c.text(name, x, sy, 1, 1, amber);
        }
    }
}
