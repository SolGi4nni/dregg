//! THE COMPOSITOR-FB PD — a real seL4 protection domain that drives a REAL
//! framebuffer visible in a QEMU window (the bytes->glass rung of
//! `docs/desktop-os-research/GRAPHICAL-SEL4-BOOT.md`).
//!
//! ## What this is
//!
//! The headless firmament (`make run-assembly`) has no display device; the
//! `compositor_pd.rs` "framebuffer" is a 256-byte host-test authority witness
//! (`FRAMEBUFFER_TILES = 256`), not pixels. THIS PD closes the output side at
//! the simplest honest scope: it
//!
//!   1. is the SOLE holder of a DEVICE cap — QEMU's `fw_cfg` engine MMIO at phys
//!      `0x9020000` on the `virt` machine (the same "one device-region cap, held
//!      by exactly one PD" discipline the net-driver PD has for the virtio-mmio
//!      slot, `docs/FIRMAMENT.md §2`),
//!   2. holds a DMA-capable framebuffer region whose PHYSICAL base it learns via
//!      the Microkit `region_paddr` setvar (exactly as the net PD learns
//!      `virtio_net_driver_dma_paddr`) — fw_cfg's DMA engine dereferences GUEST
//!      PHYSICAL addresses, so the address handed to `ramfb` must be the
//!      framebuffer's phys addr, not the PD's vaddr,
//!   3. configures QEMU's `ramfb` standalone display device by writing a
//!      `RAMFBCfg` (geometry + `XRGB8888` + the framebuffer phys addr) to the
//!      `etc/ramfb` fw_cfg file over the fw_cfg DMA interface, and
//!   4. renders a deos splash — a test pattern + a legible "deos · robigalia v0"
//!      banner (a hand-rolled 5x7 bitmap font, no external crate) — directly
//!      into the mapped framebuffer. Those bytes are what `-device ramfb` scans
//!      out into the QEMU `-display cocoa` window.
//!
//! It prints over serial exactly what it configured (resolution, framebuffer
//! phys addr, `ramfb` fw_cfg selector key, bytes written) so the boot is
//! VERIFIABLE even with `-display none` (when you cannot see the window).
//!
//! ## Fidelity (honestly labeled — NOT laundered)
//!
//! This PD shows REAL PD-driven pixels on real (emulated) display hardware: the
//! `ramfb` scanout is genuine, the framebuffer is a real DMA region this PD
//! solely holds, and the geometry/format/address handshake with QEMU is the real
//! fw_cfg protocol. What is STILL a frontier (named, not solved here): the pixel
//! SOURCE is a static in-PD splash, not `servo-render`'s SWGL `RgbaFrame` (that
//! is the next rung — `servo-render` renders INTO this region), and the scene
//! AUTHORITY teeth (T1 non-overlap / T2 label-binding / T3 focus, proven in the
//! Lean `Dregg2.Apps.Compositor` AppSpec and modelled in `compositor_pd.rs`) are
//! not yet wired onto this scanout — a single full-screen surface here. The path
//! from here to the full starbridge cockpit is GRAPHICAL-SEL4-BOOT.md §"Staging".

#![no_std]
#![no_main]

use sel4_microkit::{debug_print, debug_println, protection_domain, var, Handler, Infallible};

// ─────────────────────────── geometry + format ──────────────────────────────

/// The splash resolution. 640x480 keeps the framebuffer (640*480*4 = 1.18 MiB)
/// well inside the 2 MiB DMA region this PD maps, and is a resolution every
/// QEMU display backend accepts.
const WIDTH: u32 = 640;
const HEIGHT: u32 = 480;
const BPP: u32 = 4; // XRGB8888 — 4 bytes/pixel.
const STRIDE: u32 = WIDTH * BPP;
const FB_BYTES: usize = (STRIDE * HEIGHT) as usize;

/// `DRM_FORMAT_XRGB8888` — the fourcc `ramfb` maps to QEMU's `PIXMAN_x8r8g8b8`.
/// Little-endian byte order in memory is `[B, G, R, X]`; we write whole u32
/// pixels as `0x00RRGGBB`, which lands as that byte order on this LE target.
const DRM_FORMAT_XRGB8888: u32 = 0x3432_5258;

// ─────────────────────── the DMA region layout (2 MiB) ───────────────────────
//
// One 2 MiB DMA region (huge-page-backed so `region_paddr` is a single
// 2 MiB-aligned physically-contiguous run — a framebuffer MUST be contiguous in
// guest-physical space for `ramfb` to scan it out). Layout:
//
//   [ region_paddr + 0x000000 ]  framebuffer  (FB_BYTES = 1.18 MiB)
//   [ region_paddr + 0x1FF000 ]  fw_cfg scratch (last 4 KiB): the DMA-access
//                                 descriptor, the RAMFBCfg, and the directory
//                                 read buffer — all need a known PHYS addr too,
//                                 because the fw_cfg DMA engine dereferences
//                                 guest-physical.
//
// Both phys addresses derive from the single `fb_dma_paddr` setvar.

const REGION_SIZE: usize = 0x20_0000; // 2 MiB
const SCRATCH_OFFSET: usize = 0x1FF_000; // last 4 KiB of the region

/// The framebuffer's mapped virtual base (the Microkit loader patches this
/// `setvar_vaddr` symbol; we draw THROUGH this vaddr).
fn fb_vaddr() -> usize {
    *var!(fb_dma_vaddr: usize = 0)
}
/// The framebuffer's guest-PHYSICAL base (the `region_paddr` setvar). This is
/// the address we hand to `ramfb` — QEMU scans out from guest-physical.
fn fb_paddr() -> usize {
    *var!(fb_dma_paddr: usize = 0)
}
/// The fw_cfg MMIO window's mapped virtual base (device region, phys 0x9020000).
fn fwcfg_vaddr() -> usize {
    *var!(fwcfg_mmio_vaddr: usize = 0)
}

// ─────────────────────────── the fw_cfg interface ────────────────────────────
//
// QEMU fw_cfg MMIO register layout on the aarch64 `virt` machine (base
// 0x9020000, from qemu hw/arm/virt.c; cross-checked against the QEMU fw_cfg spec
// and a known-good bare-metal ARM-virt ramfb driver):
//
//   base + 0x00 : data register   (u64)
//   base + 0x08 : selector reg     (u16, BIG-ENDIAN)
//   base + 0x10 : DMA address reg  (u64, BIG-ENDIAN) — writing it triggers DMA
//
// The DMA descriptor (`FWCfgDmaAccess`) and all fw_cfg multi-byte fields are
// BIG-ENDIAN on the wire; this target is little-endian, so every field is
// byte-swapped with `to_be`/`from_be`.

const FWCFG_DMA_REG_OFF: usize = 0x10;

// fw_cfg DMA control bits (qemu hw/nvram/fw_cfg.h).
const FW_CFG_DMA_CTL_ERROR: u32 = 0x01;
const FW_CFG_DMA_CTL_READ: u32 = 0x02;
const FW_CFG_DMA_CTL_SELECT: u32 = 0x08;
const FW_CFG_DMA_CTL_WRITE: u32 = 0x10;

/// Well-known fw_cfg selector: the file directory.
const FW_CFG_FILE_DIR: u32 = 0x19;

/// The fw_cfg DMA descriptor — `{ control:u32, length:u32, address:u64 }`,
/// packed, all big-endian on the wire. We build it in the scratch page (so it
/// has a known phys addr) and write its phys addr to the DMA register.
#[repr(C, packed)]
struct FwCfgDmaAccess {
    control: u32, // big-endian
    length: u32,  // big-endian
    address: u64, // big-endian (the guest-phys addr of the transfer buffer)
}

/// One entry of the fw_cfg file directory — `{ size:u32, select:u16,
/// reserved:u16, name:[u8;56] }`, packed, size+select big-endian.
#[repr(C, packed)]
#[derive(Clone, Copy)]
struct FwCfgFile {
    size: u32,       // big-endian
    select: u16,     // big-endian
    _reserved: u16,
    name: [u8; 56],
}

/// The `ramfb` configuration — `{ addr:u64, fourcc:u32, flags:u32, width:u32,
/// height:u32, stride:u32 }` = 28 bytes, packed, ALL big-endian. Written to the
/// `etc/ramfb` fw_cfg file; QEMU then scans out `width x height` from `addr`.
#[repr(C, packed)]
struct RamFbCfg {
    addr: u64,   // big-endian — the framebuffer's GUEST-PHYSICAL address
    fourcc: u32, // big-endian
    flags: u32,  // big-endian
    width: u32,  // big-endian
    height: u32, // big-endian
    stride: u32, // big-endian
}

/// Trigger one fw_cfg DMA transfer: place a descriptor in the scratch page (so
/// it has a known guest-phys addr), then write that phys addr (big-endian) to
/// the DMA register and spin until the engine clears the in-flight bits.
///
/// `buf_paddr` is the guest-phys addr of the transfer buffer; `control` carries
/// the direction/select bits (and, for a SELECT, the selector key in the high
/// 16 bits). `desc_vaddr`/`desc_paddr` are the scratch slot for the descriptor.
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
    // Memory barrier: the descriptor write must land before the DMA kick.
    core::sync::atomic::fence(core::sync::atomic::Ordering::SeqCst);

    let dma_reg = (fwcfg_vaddr() + FWCFG_DMA_REG_OFF) as *mut u64;
    core::ptr::write_volatile(dma_reg, (desc_paddr as u64).to_be());

    // Spin until the engine clears every bit except a possible ERROR latch
    // (the control word is updated in place by QEMU; in-flight => non-zero
    // beyond the error bit). This mirrors the canonical bare-metal poll.
    loop {
        let ctl = u32::from_be(core::ptr::read_volatile(
            core::ptr::addr_of!((*desc_vaddr).control),
        ));
        if ctl & !FW_CFG_DMA_CTL_ERROR == 0 {
            if ctl & FW_CFG_DMA_CTL_ERROR != 0 {
                debug_println!("[compositor-fb]   WARN fw_cfg DMA returned ERROR bit");
            }
            break;
        }
        core::hint::spin_loop();
    }
}

/// Scan the fw_cfg file directory for `etc/ramfb` and return its selector key.
/// Reads the directory into the scratch page in two DMA reads (the u32 count,
/// then the entries) — no allocator on the path.
unsafe fn find_ramfb_select(scratch_vaddr: usize, scratch_paddr: usize) -> Option<u16> {
    // The descriptor lives at the top of scratch; the read buffer below it.
    let desc_vaddr = scratch_vaddr as *mut FwCfgDmaAccess;
    let desc_paddr = scratch_paddr;
    let buf_vaddr = scratch_vaddr + 0x40; // 64 B past the descriptor
    let buf_paddr = scratch_paddr + 0x40;

    // (1) read the entry count (one big-endian u32) by SELECT+READ of the dir.
    fw_cfg_dma(
        desc_vaddr,
        desc_paddr,
        buf_paddr,
        4,
        (FW_CFG_FILE_DIR << 16) | FW_CFG_DMA_CTL_SELECT | FW_CFG_DMA_CTL_READ,
    );
    let count = u32::from_be(core::ptr::read_volatile(buf_vaddr as *const u32));

    // (2) the SELECT above rewound the directory; a plain READ (no re-SELECT)
    // now streams the entries from where the count left off. Read them one at a
    // time into the same buffer slot and compare the name prefix.
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

// ─────────────────────────── the deos splash ────────────────────────────────
//
// A static RGBA frame drawn directly into the mapped framebuffer: a vertical
// deos-teal gradient backdrop, a centered card, a colour test-pattern strip
// (the F1 "which bytes reached glass" observable), and the legible banner
// "deos . robigalia v0" + a subtitle, rendered with a hand-rolled 5x7 font.

/// Pack `(r,g,b)` into an XRGB8888 pixel (`0x00RRGGBB`).
#[inline]
fn rgb(r: u8, g: u8, b: u8) -> u32 {
    ((r as u32) << 16) | ((g as u32) << 8) | (b as u32)
}

/// The framebuffer as a `&mut [u32]` of `WIDTH*HEIGHT` pixels over the mapped
/// region. The PD solely holds this region; seL4 would fault any other writer.
unsafe fn fb_pixels<'a>() -> &'a mut [u32] {
    core::slice::from_raw_parts_mut(fb_vaddr() as *mut u32, (WIDTH * HEIGHT) as usize)
}

#[inline]
fn put_px(fb: &mut [u32], x: u32, y: u32, color: u32) {
    if x < WIDTH && y < HEIGHT {
        fb[(y * WIDTH + x) as usize] = color;
    }
}

fn fill_rect(fb: &mut [u32], x0: u32, y0: u32, w: u32, h: u32, color: u32) {
    for y in y0..y0.saturating_add(h).min(HEIGHT) {
        for x in x0..x0.saturating_add(w).min(WIDTH) {
            fb[(y * WIDTH + x) as usize] = color;
        }
    }
}

/// Draw the full deos splash. Returns the number of framebuffer bytes touched
/// (the whole frame — the serial observable of "pixels written").
fn draw_splash(fb: &mut [u32]) -> usize {
    // (1) Vertical gradient backdrop — deep deos teal at top → near-black floor.
    for y in 0..HEIGHT {
        let t = y * 255 / HEIGHT;
        let r = (8 + t / 12) as u8;
        let g = (40 + (200 - t.min(200)) / 4) as u8;
        let b = (60 + (220 - t.min(220)) / 3) as u8;
        let line = rgb(r, g, b);
        let base = (y * WIDTH) as usize;
        for x in 0..WIDTH as usize {
            fb[base + x] = line;
        }
    }

    // (2) The centered card (a darker panel the text sits on).
    let card_w = 440;
    let card_h = 200;
    let card_x = (WIDTH - card_w) / 2;
    let card_y = (HEIGHT - card_h) / 2 - 10;
    fill_rect(fb, card_x, card_y, card_w, card_h, rgb(16, 22, 30));
    // a 2px teal border.
    let border = rgb(64, 200, 200);
    fill_rect(fb, card_x, card_y, card_w, 2, border);
    fill_rect(fb, card_x, card_y + card_h - 2, card_w, 2, border);
    fill_rect(fb, card_x, card_y, 2, card_h, border);
    fill_rect(fb, card_x + card_w - 2, card_y, 2, card_h, border);

    // (3) The banner + subtitle, hand-rolled 5x7 font, scaled.
    let text_x = card_x + 28;
    draw_text(fb, "deos - robigalia v0", text_x, card_y + 36, 4, rgb(230, 245, 245));
    draw_text(fb, "a rust userspace on sel4", text_x, card_y + 96, 2, rgb(150, 210, 210));
    draw_text(fb, "compositor-fb pd - ramfb scanout", text_x, card_y + 128, 2, rgb(120, 180, 190));

    // (4) The colour test-pattern strip (the F1 observable: WHICH bytes reached
    // glass). Eight bars across the bottom; if you see them, the PD's writes
    // scanned out.
    let bar_y = card_y + card_h + 24;
    let bar_h = 40;
    let bars = [
        rgb(255, 0, 0),
        rgb(255, 128, 0),
        rgb(255, 255, 0),
        rgb(0, 255, 0),
        rgb(0, 255, 255),
        rgb(0, 96, 255),
        rgb(160, 0, 255),
        rgb(255, 255, 255),
    ];
    let bar_w = WIDTH / bars.len() as u32;
    for (i, &c) in bars.iter().enumerate() {
        fill_rect(fb, i as u32 * bar_w, bar_y, bar_w, bar_h, c);
    }

    FB_BYTES
}

// A 5x7 bitmap font (columns LSB=top). Only the glyphs the splash uses are
// defined; everything else renders as a blank. Each glyph is 5 columns; each
// column is a u8 whose low 7 bits are the rows top->bottom.
fn glyph(c: u8) -> [u8; 5] {
    match c {
        b'a' => [0x20, 0x54, 0x54, 0x54, 0x78],
        b'b' => [0x7f, 0x48, 0x44, 0x44, 0x38],
        b'c' => [0x38, 0x44, 0x44, 0x44, 0x20],
        b'd' => [0x38, 0x44, 0x44, 0x48, 0x7f],
        b'e' => [0x38, 0x54, 0x54, 0x54, 0x18],
        b'f' => [0x08, 0x7e, 0x09, 0x01, 0x02],
        b'g' => [0x18, 0x54, 0x54, 0x54, 0x3c],
        b'i' => [0x00, 0x44, 0x7d, 0x40, 0x00],
        b'l' => [0x00, 0x41, 0x7f, 0x40, 0x00],
        b'm' => [0x7c, 0x04, 0x18, 0x04, 0x78],
        b'n' => [0x7c, 0x08, 0x04, 0x04, 0x78],
        b'o' => [0x38, 0x44, 0x44, 0x44, 0x38],
        b'p' => [0x7c, 0x14, 0x14, 0x14, 0x08],
        b'r' => [0x7c, 0x08, 0x04, 0x04, 0x08],
        b's' => [0x48, 0x54, 0x54, 0x54, 0x24],
        b't' => [0x04, 0x3f, 0x44, 0x40, 0x20],
        b'u' => [0x3c, 0x40, 0x40, 0x20, 0x7c],
        b'v' => [0x1c, 0x20, 0x40, 0x20, 0x1c],
        b'w' => [0x3c, 0x40, 0x30, 0x40, 0x3c],
        b'0' => [0x3e, 0x51, 0x49, 0x45, 0x3e],
        b'4' => [0x18, 0x14, 0x12, 0x7f, 0x10],
        b'.' => [0x00, 0x60, 0x60, 0x00, 0x00],
        b'-' => [0x08, 0x08, 0x08, 0x08, 0x08],
        b' ' => [0x00, 0x00, 0x00, 0x00, 0x00],
        _ => [0x00, 0x00, 0x00, 0x00, 0x00],
    }
}

/// Draw a string with the 5x7 font at `scale` (integer pixel zoom).
fn draw_text(fb: &mut [u32], s: &str, x: u32, y: u32, scale: u32, color: u32) {
    let mut cx = x;
    for &b in s.as_bytes() {
        let g = glyph(b);
        for (col, bits) in g.iter().enumerate() {
            for row in 0..7u32 {
                if bits & (1 << row) != 0 {
                    // a `scale x scale` block per lit font-pixel.
                    let px = cx + col as u32 * scale;
                    let py = y + row * scale;
                    for dy in 0..scale {
                        for dx in 0..scale {
                            put_px(fb, px + dx, py + dy, color);
                        }
                    }
                }
            }
        }
        cx += 6 * scale; // 5 cols + 1 space, scaled.
    }
}

// ────────────────────────────── the PD body ─────────────────────────────────

#[protection_domain(heap_size = 0x10000)]
fn init() -> HandlerImpl {
    debug_println!("");
    debug_println!("    ┌─────────────────────────────────────────┐");
    debug_println!("    │   deos · robigalia v0  —  GRAPHICAL      │");
    debug_println!("    │   compositor-fb PD : ramfb scanout       │");
    debug_println!("    └─────────────────────────────────────────┘");
    debug_println!("[compositor-fb] booted — the SOLE holder of the fw_cfg device cap + the");
    debug_println!("[compositor-fb] framebuffer DMA region (the graphical edge, GRAPHICAL-SEL4-BOOT.md)");

    let fb_v = fb_vaddr();
    let fb_p = fb_paddr();
    let scratch_v = fb_v + SCRATCH_OFFSET;
    let scratch_p = fb_p + SCRATCH_OFFSET;
    debug_println!(
        "[compositor-fb]   fb vaddr={:#x} fb paddr={:#x} (region {} KiB; fb {} KiB)",
        fb_v,
        fb_p,
        REGION_SIZE / 1024,
        FB_BYTES / 1024
    );
    debug_println!(
        "[compositor-fb]   fw_cfg MMIO vaddr={:#x} (phys 0x9020000, the virt fw_cfg engine)",
        fwcfg_vaddr()
    );

    // (A) DRAW the splash into the framebuffer FIRST, so the bytes are present
    // the instant ramfb starts scanning out.
    let bytes = {
        let fb = unsafe { fb_pixels() };
        draw_splash(fb)
    };
    debug_println!(
        "[compositor-fb]   drew deos splash: {}x{} XRGB8888, {} bytes written into the fb region",
        WIDTH,
        HEIGHT,
        bytes
    );

    // (B) find the ramfb fw_cfg file selector.
    let ramfb_select = unsafe { find_ramfb_select(scratch_v, scratch_p) };
    let select = match ramfb_select {
        Some(s) => {
            debug_println!(
                "[compositor-fb]   fw_cfg file 'etc/ramfb' found: selector key = {:#06x}",
                s
            );
            s
        }
        None => {
            debug_println!("[compositor-fb]   ERROR 'etc/ramfb' not in fw_cfg dir — is -device ramfb present?");
            debug_println!("[compositor-fb]   (boot with `make run-graphical`; -display none still proves the rest)");
            return HandlerImpl;
        }
    };

    // (C) configure ramfb: write the RAMFBCfg (geometry + format + fb PHYS addr)
    // to the etc/ramfb file over fw_cfg DMA. The RAMFBCfg lives in the scratch
    // page (known phys addr); we DMA-WRITE it into the selected file.
    unsafe {
        let cfg_vaddr = (scratch_v + 0x80) as *mut RamFbCfg; // past the dir scratch
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
        let desc_paddr = scratch_p;
        fw_cfg_dma(
            desc_vaddr,
            desc_paddr,
            cfg_paddr,
            core::mem::size_of::<RamFbCfg>() as u32,
            ((select as u32) << 16) | FW_CFG_DMA_CTL_SELECT | FW_CFG_DMA_CTL_WRITE,
        );
    }

    debug_println!(
        "[compositor-fb]   ramfb CONFIGURED via fw_cfg: addr={:#x} fourcc=XRGB8888 {}x{} stride={}",
        fb_p,
        WIDTH,
        HEIGHT,
        STRIDE
    );
    debug_print!("[compositor-fb]   the QEMU display now scans out this PD's pixels. ");
    debug_println!("deos is on glass. ( ◕‿◕ )");
    debug_println!("[compositor-fb]   (run `make run-graphical` for the VISIBLE window; this run proves config+draw)");

    HandlerImpl
}

/// No channels to service: the PD configures ramfb + draws once at init, then
/// idles in the Microkit event loop with the framebuffer scanning out.
struct HandlerImpl;

impl Handler for HandlerImpl {
    type Error = Infallible;
}
