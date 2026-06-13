//! THE BOOT TEST — the same-code claim, CONTINUOUSLY CHECKED.
//!
//! `docs/DREGG-DESKTOP-OS.md §3` + §6 R1 (TRACK 0, the SEMIHOST fulcrum): the
//! SAME protection-domain (PD) source that runs on real seL4 boots here on the
//! host [`EmulatedKernel`] under plain `cargo test` — no QEMU, no nightly, no
//! build-std. This file boots a small PD set on the emulator and proves a PD's
//! `init()` + `notified` bodies actually run:
//!
//!   1. **`m0-hello`** — a PD that prints the dregg-robigalia banner at `init()`
//!      and idles (the [`sel4/dregg-pd/m0-hello`] body, the SAME text).
//!   2. **the 2-PD notify slice** — PD-A `Signal`s a Notification; PD-B `Wait`s,
//!      wakes in its `notified` body, and records that it ran by writing a
//!      sentinel into a shared region (the `memory_region_symbol!` path). This
//!      exercises the §3 `Notified` event end-to-end across two PD threads
//!      sharing ONE kernel.
//!
//! Both run as host threads over ONE [`EmulatedKernel`], so a `notify` in PD-A
//! reaches the SAME Notification object PD-B `Wait`s on — the faithful seL4
//! property that two PDs invoke the same kernel object. The fidelity is
//! genuine-`n = 1`: the wake is one condvar signal under the held kernel lock,
//! the shared region is one host buffer. The ONE deliberate non-fidelity — v0
//! host threads share an address space — is honestly labeled
//! ([`EmulatedKernel::ISOLATION_FIDELITY`]), NOT laundered.

use std::sync::Arc;

use dregg_firmament::emulated_kernel::EmulatedKernel;
use dregg_firmament::microkit_facade::{
    Channel, ChannelSet, ChannelTable, ChannelWiring, EventLoop, Handler, MessageInfo,
    NullHandler, ProtectionDomain, Region,
};
use dregg_firmament::memory_region_symbol;

// ===========================================================================
// PD #1 — m0-hello. The SAME body as sel4/dregg-pd/m0-hello/src/main.rs: it
// prints the banner at init() and returns a handler that services no channels.
// On real Microkit this is `#[protection_domain] fn init() -> HandlerImpl`; on
// the semihost it is the closure ProtectionDomain::spawn runs. The PRINTED
// TEXT and the control flow are identical — that is the same-code claim.
// ===========================================================================

/// `m0-hello`'s `init()` — print the boot banner, return an idle handler. This
/// is the literal m0 body (debug prints → a `NullHandler`); on the semihost the
/// prints go to stdout under `cargo test -- --nocapture`.
fn m0_hello_init() -> (NullHandler, EventLoop) {
    println!();
    println!("    ┌─────────────────────────────────────────┐");
    println!("    │   dregg robigalia v0  (semihost)         │");
    println!("    │   a Rust userspace on the EmulatedKernel │");
    println!("    └─────────────────────────────────────────┘");
    println!();
    println!("[m0] protection domain booted on the EmulatedKernel");
    println!("[m0] capabilities all the way down ( ◕‿◕ )");
    // An idle PD: no notifications to service. The event loop returns at once,
    // exactly as m0 idles in the Microkit event loop with no channels.
    (NullHandler, EventLoop::new(EmulatedKernel::new(), vec![]))
}

#[test]
fn boot_m0_hello_on_the_emulated_kernel() {
    // Spawn the m0 PD on its own host thread; it prints and returns. `steps = 0`
    // because m0 services no events — it boots, prints, idles. Joining the
    // thread proves init() ran to completion on the EmulatedKernel.
    let pd = ProtectionDomain::spawn("m0-hello", m0_hello_init, 0);
    pd.join().expect("m0-hello PD booted and idled");
}

// ===========================================================================
// PD set #2 — the 2-PD notify slice. PD-A Signals; PD-B Waits + wakes. This is
// the §3 / §6-R1 "2-PD notify slice (PD-A Signals a Notification, PD-B Waits +
// wakes)" — the minimal proof that init() AND notified() bodies run on the
// EmulatedKernel, with a Channel mapping onto an emulated Notification cap.
// ===========================================================================

/// PD-B's handler — it owns a shared region and, when `notified`, writes a
/// sentinel + the badge it saw, so the harness can observe that its `notified`
/// body actually ran on the wake. This is a faithful Microkit `notified`
/// dispatch: the body reacts to the channel set and touches its shared memory.
struct WakeRecorder {
    /// The shared region PD-B writes its "I woke" sentinel into (the
    /// `memory_region_symbol!`-mapped buffer the harness reads).
    witness: Region,
}

impl Handler for WakeRecorder {
    fn notified(&mut self, channels: ChannelSet) {
        // PD-B woke. Record (a) a liveness sentinel and (b) which channel fired,
        // into the shared region — the SAME `with_mut` (`thread: &mut [u8]`)
        // access a real PD makes on its mapped region.
        println!("[pd-b] notified on channels {:?} — the wake fired", channels);
        self.witness.with_mut(|buf| {
            buf[0] = 0xB0; // 'B' woke
            // The low byte of the badge = the channel index bit PD-A signalled.
            buf[1] = (channels.bits() & 0xFF) as u8;
        });
    }
}

#[test]
fn boot_two_pd_notify_slice() {
    // ── The firmament wires the slice at boot (the `.system`-file equivalent). ──
    // ONE kernel both PDs share. PD-A and PD-B are on the SAME box (n = 1).
    let kernel = EmulatedKernel::new();

    // The Notification cap channel 5 maps to (Microkit: a notification cap the
    // loader patches into both PDs). PD-A signals it; PD-B waits on it.
    let notif = kernel.create_notification();
    const NOTIFY_CHANNEL: usize = 5;

    // The shared region PD-B records its wake into (the `memory_region_symbol!`
    // buffer mapped into PD-B; here also read by the harness as the observable).
    let witness_region = kernel.create_region(2);

    // PD-A's channel table: channel 5 → the notification object. (PD-B waits on
    // the notification directly via its EventLoop, the §3 Notified path, so it
    // needs no Channel handle of its own — only the SIGNALLER names a Channel to
    // `notify`. The firmament wired both ends to one kernel cap: that single
    // shared notification is what makes A's `notify` reach B's `wait`.)
    let mut pd_a_table = ChannelTable::new();
    pd_a_table.wire(
        NOTIFY_CHANNEL,
        ChannelWiring { notification: notif, endpoint: None },
    );
    let pd_a_table = Arc::new(pd_a_table);

    // ── PD-B: init() arms the wake-recorder + an event loop on channel 5. ──
    let kernel_b = kernel.clone();
    let pd_b = ProtectionDomain::spawn(
        "pd-b-waiter",
        move || {
            println!("[pd-b] init — arming the notify wait on channel {NOTIFY_CHANNEL}");
            // The PD's `memory_region_symbol!` mapping onto its shared region.
            let witness = memory_region_symbol!(kernel_b, witness_region);
            let handler = WakeRecorder { witness };
            // Block on channel 5's notification (the Notified event).
            let evloop = EventLoop::new(kernel_b.clone(), vec![notif]);
            (handler, evloop)
        },
        1, // service exactly one notification, then return
    );

    // ── PD-A: init() signals channel 5 (after a beat so B is parked), idles. ──
    let kernel_a = kernel.clone();
    let pd_a = ProtectionDomain::spawn(
        "pd-a-signaller",
        move || {
            println!("[pd-a] init — signalling channel {NOTIFY_CHANNEL}");
            // A small beat so PD-B reaches its `wait` and parks (not load-bearing
            // — the badge-OR accumulator means a signal before the wait is not
            // lost — but it exercises the genuine blocking rendezvous).
            std::thread::sleep(std::time::Duration::from_millis(20));
            // The SAME `Channel::notify()` a real PD calls. It signals the wired
            // notification with channel 5's badge bit, waking PD-B.
            let ch: Channel = Channel::bound(NOTIFY_CHANNEL, kernel_a.clone(), pd_a_table);
            ch.notify();
            println!("[pd-a] signalled — PD-B should wake");
            // PD-A has nothing to service; it idles.
            (NullHandler, EventLoop::new(kernel_a.clone(), vec![]))
        },
        0,
    );

    // ── Join both PDs and check the slice ran. ──
    pd_a.join().expect("PD-A signalled");
    pd_b.join().expect("PD-B woke and ran its notified body");

    // THE OBSERVABLE: PD-B's `notified` body ran (sentinel 0xB0) and saw channel
    // 5's badge bit (1 << 5 = 0x20). The harness reads the shared region PD-B
    // wrote — proving the notify crossed from PD-A's thread to PD-B's wake on
    // the SAME EmulatedKernel notification object.
    let witness = kernel.region_read(witness_region).expect("witness region");
    assert_eq!(witness[0], 0xB0, "PD-B's notified body must have run");
    assert_eq!(
        witness[1],
        (1u64 << NOTIFY_CHANNEL) as u8,
        "PD-B must have seen channel {NOTIFY_CHANNEL}'s badge bit"
    );

    println!(
        "NOTIFY SLICE: PD-A Channel::notify(ch{NOTIFY_CHANNEL}) → PD-B woke, \
         saw badge {:#04x} — init()+notified() ran on the EmulatedKernel ( ˘▾˘ )",
        witness[1]
    );
    // Quietly assert the honest fidelity note travels with the code.
    let _ = (MessageInfo::default(), EmulatedKernel::ISOLATION_FIDELITY);
}
