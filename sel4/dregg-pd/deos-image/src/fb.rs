//! The framebuffer: the fw_cfg/ramfb device handshake (so QEMU scans out the
//! pixels this PD draws) + a `Canvas` of drawing primitives the screens paint
//! with. The device half is the SAME protocol the compositor-fb PD proved
//! (docs/desktop-os-research/GRAPHICAL-SEL4-BOOT.md §3); here it is factored so
//! the screens can repaint the framebuffer live on every keypress.

use sel4_microkit::{debug_println, var};

use crate::font;

// ─────────────────────────── geometry + format ──────────────────────────────

pub const WIDTH: u32 = 800;
pub const HEIGHT: u32 = 600;
const BPP: u32 = 4;
pub const STRIDE: u32 = WIDTH * BPP;

/// `DRM_FORMAT_XRGB8888` — the fourcc ramfb maps to QEMU's `PIXMAN_x8r8g8b8`.
/// We write whole u32 pixels as `0x00RRGGBB`.
const DRM_FORMAT_XRGB8888: u32 = 0x3432_5258;

// The framebuffer region is 4 MiB (800*600*4 = 1.83 MiB fits; the last 4 KiB is
// the fw_cfg DMA scratch, at SCRATCH_OFFSET). Huge-page-backed so `region_paddr`
// is one contiguous run (a scanned-out framebuffer must be contiguous in
// guest-physical space). See deos-tutorial.system's <memory_region fb_dma>.
const SCRATCH_OFFSET: usize = 0x3FF_000; // last 4 KiB of the 4 MiB region

fn fb_vaddr() -> usize {
    *var!(fb_dma_vaddr: usize = 0)
}
fn fb_paddr() -> usize {
    *var!(fb_dma_paddr: usize = 0)
}
fn fwcfg_vaddr() -> usize {
    *var!(fwcfg_mmio_vaddr: usize = 0)
}

// ─────────────────────────── the fw_cfg interface ────────────────────────────
// (verbatim protocol of compositor-fb: MMIO base 0x9020000, big-endian fields.)

const FWCFG_DMA_REG_OFF: usize = 0x10;
const FW_CFG_DMA_CTL_ERROR: u32 = 0x01;
const FW_CFG_DMA_CTL_READ: u32 = 0x02;
const FW_CFG_DMA_CTL_SELECT: u32 = 0x08;
const FW_CFG_DMA_CTL_WRITE: u32 = 0x10;
const FW_CFG_FILE_DIR: u32 = 0x19;

#[repr(C, packed)]
struct FwCfgDmaAccess {
    control: u32,
    length: u32,
    address: u64,
}

#[repr(C, packed)]
#[derive(Clone, Copy)]
struct FwCfgFile {
    size: u32,
    select: u16,
    _reserved: u16,
    name: [u8; 56],
}

#[repr(C, packed)]
struct RamFbCfg {
    addr: u64,
    fourcc: u32,
    flags: u32,
    width: u32,
    height: u32,
    stride: u32,
}

unsafe fn fw_cfg_dma(
    desc_vaddr: *mut FwCfgDmaAccess,
    desc_paddr: usize,
    buf_paddr: usize,
    length: u32,
    control: u32,
) {
    core::ptr::write_volatile(
        desc_vaddr,
        FwCfgDmaAccess {
            control: control.to_be(),
            length: length.to_be(),
            address: (buf_paddr as u64).to_be(),
        },
    );
    core::sync::atomic::fence(core::sync::atomic::Ordering::SeqCst);
    let dma_reg = (fwcfg_vaddr() + FWCFG_DMA_REG_OFF) as *mut u64;
    core::ptr::write_volatile(dma_reg, (desc_paddr as u64).to_be());
    loop {
        let ctl = u32::from_be(core::ptr::read_volatile(core::ptr::addr_of!(
            (*desc_vaddr).control
        )));
        if ctl & !FW_CFG_DMA_CTL_ERROR == 0 {
            if ctl & FW_CFG_DMA_CTL_ERROR != 0 {
                debug_println!("[deos-image]   WARN fw_cfg DMA ERROR bit");
            }
            break;
        }
        core::hint::spin_loop();
    }
}

unsafe fn find_ramfb_select(scratch_vaddr: usize, scratch_paddr: usize) -> Option<u16> {
    let desc_vaddr = scratch_vaddr as *mut FwCfgDmaAccess;
    let desc_paddr = scratch_paddr;
    let buf_vaddr = scratch_vaddr + 0x40;
    let buf_paddr = scratch_paddr + 0x40;
    fw_cfg_dma(
        desc_vaddr,
        desc_paddr,
        buf_paddr,
        4,
        (FW_CFG_FILE_DIR << 16) | FW_CFG_DMA_CTL_SELECT | FW_CFG_DMA_CTL_READ,
    );
    let count = u32::from_be(core::ptr::read_volatile(buf_vaddr as *const u32));
    let want = b"etc/ramfb";
    let entry_vaddr = buf_vaddr as *mut FwCfgFile;
    for _ in 0..count {
        fw_cfg_dma(
            desc_vaddr,
            desc_paddr,
            buf_paddr,
            core::mem::size_of::<FwCfgFile>() as u32,
            FW_CFG_DMA_CTL_READ,
        );
        let file = core::ptr::read_volatile(entry_vaddr);
        let name = file.name;
        let name_matches = name.len() >= want.len()
            && &name[..want.len()] == want
            && (name.len() == want.len() || name[want.len()] == 0);
        if name_matches {
            return Some(u16::from_be(file.select));
        }
    }
    None
}

/// Configure QEMU's ramfb to scan out THIS PD's framebuffer (geometry + format +
/// guest-physical base over the fw_cfg DMA-write interface). Returns true on
/// success. Call once at init, AFTER the first frame is drawn.
pub fn configure_ramfb() -> bool {
    let fb_p = fb_paddr();
    let scratch_v = fb_vaddr() + SCRATCH_OFFSET;
    let scratch_p = fb_p + SCRATCH_OFFSET;

    let select = match unsafe { find_ramfb_select(scratch_v, scratch_p) } {
        Some(s) => {
            debug_println!("[deos-image]   fw_cfg 'etc/ramfb' selector = {:#06x}", s);
            s
        }
        None => {
            debug_println!(
                "[deos-image]   ERROR 'etc/ramfb' not found (is -device ramfb present?)"
            );
            return false;
        }
    };

    unsafe {
        let cfg_vaddr = (scratch_v + 0x80) as *mut RamFbCfg;
        let cfg_paddr = scratch_p + 0x80;
        core::ptr::write_volatile(
            cfg_vaddr,
            RamFbCfg {
                addr: (fb_p as u64).to_be(),
                fourcc: DRM_FORMAT_XRGB8888.to_be(),
                flags: 0u32.to_be(),
                width: WIDTH.to_be(),
                height: HEIGHT.to_be(),
                stride: STRIDE.to_be(),
            },
        );
        core::sync::atomic::fence(core::sync::atomic::Ordering::SeqCst);
        let desc_vaddr = scratch_v as *mut FwCfgDmaAccess;
        fw_cfg_dma(
            desc_vaddr,
            scratch_p,
            cfg_paddr,
            core::mem::size_of::<RamFbCfg>() as u32,
            ((select as u32) << 16) | FW_CFG_DMA_CTL_SELECT | FW_CFG_DMA_CTL_WRITE,
        );
    }
    debug_println!(
        "[deos-image]   ramfb CONFIGURED: addr={:#x} XRGB8888 {}x{} stride={}",
        fb_p,
        WIDTH,
        HEIGHT,
        STRIDE
    );
    true
}

// ───────────────────────────── the Canvas ───────────────────────────────────

/// Pack `(r,g,b)` into an XRGB8888 pixel.
#[inline]
pub const fn rgb(r: u8, g: u8, b: u8) -> u32 {
    ((r as u32) << 16) | ((g as u32) << 8) | (b as u32)
}

/// Linear blend `a*(1-t) .. b*t`, t in 0..=255, per channel.
#[inline]
fn lerp8(a: u8, b: u8, t: u32) -> u8 {
    let a = a as u32;
    let b = b as u32;
    ((a * (255 - t) + b * t) / 255) as u8
}

/// A live handle to the mapped framebuffer. The PD solely holds the region; seL4
/// faults any other writer. Methods clip to the framebuffer bounds.
pub struct Canvas {
    px: &'static mut [u32],
}

impl Canvas {
    /// Borrow the mapped framebuffer as a `Canvas`. Caller guarantees no aliasing
    /// (the PD draws single-threaded from one event handler).
    pub unsafe fn map() -> Self {
        let px = core::slice::from_raw_parts_mut(fb_vaddr() as *mut u32, (WIDTH * HEIGHT) as usize);
        Canvas { px }
    }

    #[inline]
    pub fn put(&mut self, x: u32, y: u32, color: u32) {
        if x < WIDTH && y < HEIGHT {
            self.px[(y * WIDTH + x) as usize] = color;
        }
    }

    pub fn rect(&mut self, x0: u32, y0: u32, w: u32, h: u32, color: u32) {
        let y1 = y0.saturating_add(h).min(HEIGHT);
        let x1 = x0.saturating_add(w).min(WIDTH);
        for y in y0..y1 {
            let base = (y * WIDTH) as usize;
            for x in x0..x1 {
                self.px[base + x as usize] = color;
            }
        }
    }

    /// A 1px-thick rectangle outline (`t` px thick).
    pub fn frame(&mut self, x: u32, y: u32, w: u32, h: u32, t: u32, color: u32) {
        self.rect(x, y, w, t, color);
        self.rect(x, y + h.saturating_sub(t), w, t, color);
        self.rect(x, y, t, h, color);
        self.rect(x + w.saturating_sub(t), y, t, h, color);
    }

    /// A full-screen vertical gradient from `top` (y=0) to `bot` (y=HEIGHT).
    pub fn vgradient(&mut self, top: (u8, u8, u8), bot: (u8, u8, u8)) {
        for y in 0..HEIGHT {
            let t = y * 255 / (HEIGHT - 1);
            let c = rgb(
                lerp8(top.0, bot.0, t),
                lerp8(top.1, bot.1, t),
                lerp8(top.2, bot.2, t),
            );
            let base = (y * WIDTH) as usize;
            for x in 0..WIDTH as usize {
                self.px[base + x] = c;
            }
        }
    }

    /// A vertical gradient confined to a rectangle (for cards / banners).
    pub fn vgradient_rect(
        &mut self,
        x: u32,
        y: u32,
        w: u32,
        h: u32,
        top: (u8, u8, u8),
        bot: (u8, u8, u8),
    ) {
        let y1 = y.saturating_add(h).min(HEIGHT);
        let x1 = x.saturating_add(w).min(WIDTH);
        for yy in y..y1 {
            let t = if h > 1 { (yy - y) * 255 / (h - 1) } else { 0 };
            let c = rgb(
                lerp8(top.0, bot.0, t),
                lerp8(top.1, bot.1, t),
                lerp8(top.2, bot.2, t),
            );
            let base = (yy * WIDTH) as usize;
            for xx in x..x1 {
                self.px[base + xx as usize] = c;
            }
        }
    }

    /// Draw one glyph at top-left `(x,y)`, integer-zoomed by `scale`.
    fn glyph_at(&mut self, c: u8, x: u32, y: u32, scale: u32, color: u32) {
        let g = font::glyph(c);
        for (row, bits) in g.iter().enumerate() {
            if *bits == 0 {
                continue;
            }
            for col in 0..8u32 {
                if bits & (0x80 >> col) != 0 {
                    let px = x + col * scale;
                    let py = y + row as u32 * scale;
                    for dy in 0..scale {
                        for dx in 0..scale {
                            self.put(px + dx, py + dy, color);
                        }
                    }
                }
            }
        }
    }

    /// Draw a string left-anchored at `(x,y)`. `track` is extra inter-glyph
    /// spacing in *source* pixels (before scaling). Returns the x past the text.
    pub fn text(&mut self, s: &str, x: u32, y: u32, scale: u32, track: u32, color: u32) -> u32 {
        let mut cx = x;
        let adv = (font::CELL_W + track) * scale;
        for &b in s.as_bytes() {
            self.glyph_at(b, cx, y, scale, color);
            cx += adv;
        }
        cx
    }

    /// The pixel width a string would occupy with `text` (for centering).
    pub fn text_w(s: &str, scale: u32, track: u32) -> u32 {
        let n = s.as_bytes().len() as u32;
        if n == 0 {
            0
        } else {
            // n glyph cells, (n-1) tracking gaps absorbed by adv; last cell's
            // trailing track is real width too — keep it simple and symmetric.
            n * (font::CELL_W + track) * scale
        }
    }

    /// Draw a string horizontally centered in `[x0, x0+w)` at top `y`.
    pub fn text_center(
        &mut self,
        s: &str,
        x0: u32,
        w: u32,
        y: u32,
        scale: u32,
        track: u32,
        color: u32,
    ) -> u32 {
        let tw = Self::text_w(s, scale, track).min(w);
        let x = x0 + (w.saturating_sub(tw)) / 2;
        self.text(s, x, y, scale, track, color)
    }
}
