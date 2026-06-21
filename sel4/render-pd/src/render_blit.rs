//! The final rung of the in-VM re-flow: RGBA (from the in-PD gpui render) →
//! XRGB8888 → the seL4 ramfb framebuffer. This is the EXACT blit loop the
//! deos-image PD uses (`dregg-pd/deos-image/src/cockpit_frame.rs::blit_frame`),
//! minus the `include_bytes!` bake — here the RGBA comes from the in-PD render,
//! not a baked asset.
//!
//! STAGED, not yet exercised: the render-PD reaches lavapipe device creation but
//! stops at the submit-thread `thrd_create` wall (WIRING.md "MEASURED RESULT"), so
//! no in-PD RGBA exists to blit yet. This module is the receiving end, ready for
//! when the `__clone`/TCB lever unblocks `vkCreateDevice` → a JIT'd render →
//! `render_scene_to_image` → these bytes. The geometry + the RGBA→XRGB8888
//! swizzle match the persvati bake exactly, so the byte-compare (the parity proof)
//! is a straight `memcmp` of this blit's input against `cockpit_frame.rgba`.
//!
//! The framebuffer-mapping half differs from deos-image: that PD is microkit
//! (`var!()` vaddrs from the .system file); this is a raw root task, so the
//! framebuffer frames are mapped from the root task's untyped/device caps at boot
//! (the compositor-fb / deos-tutorial fw_cfg+ramfb discipline). That mapping is
//! wired alongside the `__clone` TCB work — both are the same "give the root task
//! the device caps" rung — so it is intentionally a thin seam here.

/// The framebuffer geometry — equals the persvati render geometry so the blit is a
/// straight copy and the parity byte-compare is exact.
pub const WIDTH: u32 = 800;
pub const HEIGHT: u32 = 600;

/// Pack `(r,g,b)` into an XRGB8888 pixel (`0x00RRGGBB`) — the ramfb format
/// (`DRM_FORMAT_XRGB8888`). Identical to `fb::rgb` in deos-image.
#[inline]
pub const fn rgb(r: u8, g: u8, b: u8) -> u32 {
    ((r as u32) << 16) | ((g as u32) << 8) | (b as u32)
}

/// Blit one in-PD-rendered RGBA8 frame (`800×600`, row-major, no padding —
/// `WIDTH*HEIGHT*4` bytes) into the mapped XRGB8888 framebuffer the QEMU ramfb
/// engine scans out. The exact loop deos-image's `blit_frame` runs, minus the
/// bake. `fb` is the mapped framebuffer as `WIDTH*HEIGHT` u32 pixels.
///
/// Returns the number of pixels written (`WIDTH*HEIGHT`) on a correct-length
/// input, or `0` if `rgba` is the wrong length (a render/geometry mismatch — the
/// caller paints a backdrop, as deos-image does).
pub fn blit_rgba_to_framebuffer(rgba: &[u8], fb: &mut [u32]) -> usize {
    let want = (WIDTH * HEIGHT * 4) as usize;
    if rgba.len() != want || fb.len() < (WIDTH * HEIGHT) as usize {
        return 0;
    }
    for y in 0..HEIGHT {
        for x in 0..WIDTH {
            let i = ((y * WIDTH + x) * 4) as usize;
            let r = rgba[i];
            let g = rgba[i + 1];
            let b = rgba[i + 2];
            // alpha (i+3) ignored: the framebuffer is XRGB (opaque); the cockpit
            // backdrop is itself opaque so this is exact — matching deos-image.
            fb[(y * WIDTH + x) as usize] = rgb(r, g, b);
        }
    }
    (WIDTH * HEIGHT) as usize
}

// ─────────────────────────── both-polarity proof ────────────────────────────
//
// These tests exercise the REAL blit path (the function above, the one main.rs
// drives on the boot path), both polarities: a genuine in-PD frame converts
// correctly (✓), and malformed/short inputs are rejected fail-closed (✗) —
// never reading garbage or scribbling past the framebuffer.
//
// The PD crate is pinned to the bare `aarch64-sel4-roottask-musl` target (no host
// `cargo test`), so these also run via the standalone host harness
// `tests/render_blit_polarity.rs` which `include!`s this file's logic — see that
// file. Kept here too so they live next to the code they prove.
#[cfg(test)]
mod tests {
    use super::*;

    /// Build a deterministic RGBA8 frame: pixel (x,y) → (x as u8, y as u8, x^y, 255).
    fn synth_rgba() -> Vec<u8> {
        let mut v = vec![0u8; (WIDTH * HEIGHT * 4) as usize];
        for y in 0..HEIGHT {
            for x in 0..WIDTH {
                let i = ((y * WIDTH + x) * 4) as usize;
                v[i] = x as u8;
                v[i + 1] = y as u8;
                v[i + 2] = (x ^ y) as u8;
                v[i + 3] = 255;
            }
        }
        v
    }

    #[test]
    fn genuine_frame_converts_to_xrgb8888() {
        let rgba = synth_rgba();
        let mut fb = vec![0u32; (WIDTH * HEIGHT) as usize];
        let n = blit_rgba_to_framebuffer(&rgba, &mut fb);
        // ✓ every pixel written, and each XRGB8888 pixel is the exact RGB pack
        // (alpha dropped — opaque framebuffer).
        assert_eq!(n, (WIDTH * HEIGHT) as usize);
        for y in 0..HEIGHT {
            for x in 0..WIDTH {
                let idx = (y * WIDTH + x) as usize;
                let expect = rgb(x as u8, y as u8, (x ^ y) as u8);
                assert_eq!(fb[idx], expect, "pixel ({x},{y}) mismatched");
                // The high byte must be zero (XRGB: no alpha bleed).
                assert_eq!(fb[idx] & 0xFF00_0000, 0);
            }
        }
    }

    #[test]
    fn solid_clear_color_round_trips() {
        // The exact STAGE-5 render fill: every pixel rgb(11,15,26), alpha 255.
        let mut rgba = vec![0u8; (WIDTH * HEIGHT * 4) as usize];
        for px in rgba.chunks_exact_mut(4) {
            px[0] = 11; px[1] = 15; px[2] = 26; px[3] = 255;
        }
        let mut fb = vec![0u32; (WIDTH * HEIGHT) as usize];
        let n = blit_rgba_to_framebuffer(&rgba, &mut fb);
        assert_eq!(n, (WIDTH * HEIGHT) as usize);
        assert!(fb.iter().all(|&px| px == rgb(11, 15, 26)));
    }

    #[test]
    fn short_rgba_is_rejected_fail_closed() {
        // ✗ a render/geometry mismatch (too few bytes) must write NOTHING and
        // return 0 — never partial-blit or read OOB.
        let rgba = vec![0xABu8; ((WIDTH * HEIGHT * 4) - 4) as usize];
        let mut fb = vec![0xDEAD_BEEFu32; (WIDTH * HEIGHT) as usize];
        let n = blit_rgba_to_framebuffer(&rgba, &mut fb);
        assert_eq!(n, 0, "short RGBA must be rejected");
        assert!(fb.iter().all(|&px| px == 0xDEAD_BEEF), "framebuffer must be untouched");
    }

    #[test]
    fn oversized_rgba_is_rejected_fail_closed() {
        // ✗ too MANY bytes is also a mismatch — reject, don't truncate-blit.
        let rgba = vec![0x11u8; ((WIDTH * HEIGHT * 4) + 4) as usize];
        let mut fb = vec![0u32; (WIDTH * HEIGHT) as usize];
        assert_eq!(blit_rgba_to_framebuffer(&rgba, &mut fb), 0);
        assert!(fb.iter().all(|&px| px == 0));
    }

    #[test]
    fn short_framebuffer_is_rejected_fail_closed() {
        // ✗ a framebuffer smaller than the frame must be rejected, never written
        // past its end (an OOB write would be a memory-safety bug on glass).
        let rgba = synth_rgba();
        let mut fb = vec![0u32; (WIDTH * HEIGHT) as usize - 1];
        assert_eq!(blit_rgba_to_framebuffer(&rgba, &mut fb), 0);
        assert!(fb.iter().all(|&px| px == 0));
    }

    #[test]
    fn rgb_pack_is_xrgb8888() {
        assert_eq!(rgb(0x11, 0x22, 0x33), 0x0011_2233);
        assert_eq!(rgb(0xFF, 0x00, 0x00), 0x00FF_0000);
        assert_eq!(rgb(0x00, 0xFF, 0x00), 0x0000_FF00);
        assert_eq!(rgb(0x00, 0x00, 0xFF), 0x0000_00FF);
        // The X (alpha) nibble is always zero.
        assert_eq!(rgb(0xFF, 0xFF, 0xFF) & 0xFF00_0000, 0);
    }
}
