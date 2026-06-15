//! The virtio-keyboard driver: the SAME device-cap discipline the net-driver PD
//! (sel4/dregg-pd/net) and the deos-tutorial PD use, here for navigating a LIVE
//! IMAGE of cells. The PD solely holds the keyboard's virtio-mmio region + its
//! DMA region + its IRQ; a keypress raises the IRQ, which schedules the PD's
//! `notified()` handler, which drains the event queue and turns evdev keycodes
//! into navigation [`Nav`] actions.
//!
//! Unlike the tutorial's two-way (next/prev) nav, the image viewer is a real
//! object browser: UP/DOWN move BETWEEN cells in the rail, ENTER drills INTO the
//! focused cell (and pages its substances), ESC backs OUT. SPACE acts as ENTER
//! (drill / advance) so a one-key newcomer can still walk everything.
//!
//! virtio-input delivers Linux evdev events `{ event_type, code, value }`:
//!   event_type EV_KEY = 1, value 1 = press (0 = release, 2 = autorepeat).
//!   codes (linux/input-event-codes.h): SPACE=57 ENTER=28 UP=103 DOWN=108
//!   LEFT=105 RIGHT=106 ESC=1 BACKSPACE=14.

use core::ptr::NonNull;

use virtio_drivers::{
    device::input::VirtIOInput,
    transport::mmio::{MmioTransport, VirtIOHeader},
    transport::{DeviceType, Transport},
};

use sel4_microkit::{debug_println, var};
use sel4_virtio_hal_impl::HalImpl;

// The keyboard's virtio-mmio slot. We place `-device virtio-keyboard-device` on
// virtio-mmio-bus.30 (qemu_virt_aarch64 slot 30: base 0xa000000 + 30*0x200 =
// 0xa003c00; region phys 0xa003000 + OFFSET 0xc00; IRQ = 48 + 30 = 78). The
// SAME slot the deos-tutorial PD uses — one interactive graphical edge.
pub const KBD_MMIO_OFFSET: usize = 0xc00;
pub const KBD_MMIO_SIZE: usize = 0x200;
pub const KBD_DMA_SIZE: usize = 0x10_0000; // 1 MiB for the small event rings

// evdev keycodes we navigate by.
const KEY_ESC: u16 = 1;
const KEY_BACKSPACE: u16 = 14;
const KEY_ENTER: u16 = 28;
const KEY_SPACE: u16 = 57;
const KEY_UP: u16 = 103;
const KEY_LEFT: u16 = 105;
const KEY_RIGHT: u16 = 106;
const KEY_DOWN: u16 = 108;
const EV_KEY: u16 = 1;

/// A navigation intent decoded from a keypress — the verbs of an object browser.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Nav {
    /// Move focus to the previous cell in the rail (UP / LEFT).
    Up,
    /// Move focus to the next cell in the rail (DOWN / RIGHT).
    Down,
    /// Drill INTO the focused cell, or page forward through its substances
    /// (ENTER / SPACE).
    Enter,
    /// Back OUT of a drill-in (ESC / BACKSPACE).
    Back,
    /// No navigable key in this batch.
    None,
}

pub type Keyboard = VirtIOInput<HalImpl, MmioTransport<'static>>;

/// Initialise the HAL + probe the virtio-keyboard at its mmio slot. Returns the
/// driver on success; logs + returns None if the slot is empty / not an input
/// device (so the viewer can still show the image, non-interactively).
pub fn init() -> Option<Keyboard> {
    HalImpl::init(
        KBD_DMA_SIZE,
        *var!(virtio_kbd_dma_vaddr: usize = 0),
        *var!(virtio_kbd_dma_paddr: usize = 0),
    );

    let header = NonNull::new(
        (*var!(virtio_kbd_mmio_vaddr: usize = 0) + KBD_MMIO_OFFSET) as *mut VirtIOHeader,
    )?;
    let transport = match unsafe { MmioTransport::new(header, KBD_MMIO_SIZE) } {
        Ok(t) => t,
        Err(e) => {
            debug_println!("[deos-image]   keyboard mmio: no transport ({:?})", e);
            return None;
        }
    };
    debug_println!(
        "[deos-image]   virtio-kbd probe: version={:?} device_type={:?} vendor={:#x}",
        transport.version(),
        transport.device_type(),
        transport.vendor_id(),
    );
    if transport.device_type() != DeviceType::Input {
        debug_println!("[deos-image]   keyboard slot is not an Input device");
        return None;
    }
    match VirtIOInput::new(transport) {
        Ok(dev) => {
            debug_println!("[deos-image]   virtio-keyboard UP -- UP/DOWN walk cells, ENTER drills in, ESC backs out");
            Some(dev)
        }
        Err(e) => {
            debug_println!("[deos-image]   VirtIOInput::new failed ({:?})", e);
            None
        }
    }
}

/// Drain all pending events, acking the device interrupt, and fold them into a
/// single navigation intent (the last navigable press wins; releases ignored).
pub fn drain(dev: &mut Keyboard) -> Nav {
    dev.ack_interrupt();
    let mut nav = Nav::None;
    while let Some(ev) = dev.pop_pending_event() {
        if ev.event_type != EV_KEY || ev.value == 0 {
            continue; // not a key, or a release
        }
        match ev.code {
            KEY_UP | KEY_LEFT => nav = Nav::Up,
            KEY_DOWN | KEY_RIGHT => nav = Nav::Down,
            KEY_ENTER | KEY_SPACE => nav = Nav::Enter,
            KEY_ESC | KEY_BACKSPACE => nav = Nav::Back,
            _ => {}
        }
    }
    nav
}
