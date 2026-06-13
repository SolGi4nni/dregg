//! The microkit facade — the "port" the dregg PDs code against, UML-style.
//!
//! `docs/DREGG-DESKTOP-OS.md §3` + L1 (the microkernel seam, "the same-code
//! contract") specifies a **minimal `sel4-microkit`-shaped API** the dregg
//! protection domains (PDs) code against: a `#[protection_domain]`-style entry,
//! a [`Handler`] trait (`notified`/`protected`/`fault`), a [`Channel`]
//! (`notify`/`pp_call`/`irq_ack`), a [`MessageInfo`] + an IPC buffer, and
//! [`memory_region_symbol!`](crate::memory_region_symbol)-style shared memory —
//! cfg-selected **std-backed (semihost, over the [`EmulatedKernel`]) now**, real
//! seL4 later. **A PD's `init()` + `notified`/`protected` bodies are LITERALLY
//! the same text on both** — UML's `um` arch / gVisor platform pattern.
//!
//! This module is the std-backed half. Its public surface mirrors the real
//! `sel4_microkit` crate (`sel4/dregg-pd/*` codes against the genuine one;
//! `~/.cargo/git/.../crates/sel4-microkit/base/src/{channel,handler,message}.rs`
//! is the contract this matches name-for-name):
//!
//! | real `sel4_microkit`        | this facade                          |
//! |-----------------------------|--------------------------------------|
//! | `Channel::notify`           | [`Channel::notify`] → kernel Signal  |
//! | `Channel::pp_call`          | [`Channel::pp_call`] → kernel Call    |
//! | `Channel::irq_ack`          | [`Channel::irq_ack`] (no-op host stub)|
//! | `Handler::{notified,protected,fault}` | [`Handler`] (same sigs)    |
//! | `MessageInfo`               | [`MessageInfo`]                       |
//! | `ChannelSet`                | [`ChannelSet`] (badge → channels)     |
//! | `memory_region_symbol!`     | [`Region`] + the macro                |
//! | `#[protection_domain] fn init` | [`ProtectionDomain::spawn`]        |
//!
//! ## How a Channel maps to the kernel (§3: "Channels map to emulated
//! Notification/Endpoint caps")
//!
//! A [`Channel`] is a small index plus a handle to the [`EmulatedKernel`] and
//! the object ids the firmament wired for that channel at boot: a Notification
//! (for `notify`/the `Notified` event) and, if the channel is a protected-
//! procedure channel, an Endpoint (for `pp_call`). The PD names a channel by
//! index exactly as on real Microkit; the facade resolves index → kernel object.
//! The channel index is the *badge bit* the Notification ORs in on `notify`, so
//! the receiving PD's `notified(channels)` recovers WHICH channel fired —
//! matching Microkit's badge-as-channel-set encoding.

use std::collections::BTreeMap;
use std::string::String;
use std::sync::Arc;
use std::thread::{self, JoinHandle};

use crate::emulated_kernel::{EmulatedKernel, IpcError, Message, ObjectId};

/// An IPC message tag — the facade's [`MessageInfo`], mirroring
/// `sel4_microkit::MessageInfo` (`message.rs`): a small `label` + a `count` of
/// meaningful payload bytes carried alongside in the IPC buffer.
///
/// On real Microkit the payload lives in the message registers / IPC buffer; the
/// facade carries it inline in the [`Message`] the kernel rendezvous moves, and
/// [`MessageInfo`] is the *tag* (label + length) just as the real one is.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MessageInfo {
    label: u64,
    count: usize,
}

impl MessageInfo {
    /// A message tag with `label` and `count` meaningful payload bytes
    /// (mirrors `sel4_microkit::MessageInfo::new`).
    pub fn new(label: u64, count: usize) -> Self {
        MessageInfo { label, count }
    }

    /// The label associated with this message (the receiver dispatches on it).
    pub fn label(&self) -> u64 {
        self.label
    }

    /// The number of meaningful payload bytes.
    pub fn count(&self) -> usize {
        self.count
    }
}

impl Default for MessageInfo {
    fn default() -> Self {
        MessageInfo::new(0, 0)
    }
}

/// The set of channels a `notified` event covers — the facade's [`ChannelSet`],
/// mirroring `sel4_microkit::ChannelSet` (`ipc.rs`): a badge whose set bits are
/// the channel indices that fired. The badge-OR encoding is exactly Microkit's.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ChannelSet(u64);

impl ChannelSet {
    /// Does the channel `index` appear in this set?
    pub fn contains(&self, index: usize) -> bool {
        (self.0 & (1 << index)) != 0
    }

    /// Iterate the channel indices in the set (low bit first).
    pub fn iter(&self) -> impl Iterator<Item = usize> {
        let bits = self.0;
        (0..64).filter(move |i| (bits & (1 << i)) != 0)
    }

    /// The raw badge bits (for assertions/logging).
    pub fn bits(&self) -> u64 {
        self.0
    }
}

/// The wiring for one [`Channel`]: which kernel objects back its `notify` /
/// `pp_call`, recorded by the firmament at boot. A channel always has a
/// Notification (for `notify` + the `Notified` event); it has an Endpoint only
/// if it is a protected-procedure (PP) channel.
#[derive(Clone)]
pub struct ChannelWiring {
    /// The Notification object this channel signals/waits on.
    pub notification: ObjectId,
    /// The Endpoint object this channel `pp_call`s, if it is a PP channel.
    pub endpoint: Option<ObjectId>,
}

/// The per-PD channel table: index → wiring. Shared into the PD's [`Channel`]
/// handles. The firmament builds this at boot from the system description (here,
/// the boot test wires it explicitly), exactly as Microkit's loader patches each
/// PD's channel caps from the `.system` file.
#[derive(Clone, Default)]
pub struct ChannelTable {
    wiring: BTreeMap<usize, ChannelWiring>,
}

impl ChannelTable {
    /// An empty channel table.
    pub fn new() -> Self {
        ChannelTable { wiring: BTreeMap::new() }
    }

    /// Wire channel `index` to its kernel objects.
    pub fn wire(&mut self, index: usize, wiring: ChannelWiring) {
        self.wiring.insert(index, wiring);
    }

    fn get(&self, index: usize) -> Option<&ChannelWiring> {
        self.wiring.get(&index)
    }
}

/// A channel between this PD and another, identified by a channel index — the
/// facade's [`Channel`], mirroring `sel4_microkit::Channel` (`channel.rs`).
///
/// The PD names a channel by index (a `const Channel = Channel::new(1)` exactly
/// as on real Microkit); the handle additionally carries the [`EmulatedKernel`]
/// + the channel table so `notify`/`pp_call` resolve index → kernel object. On
/// real seL4 the index alone suffices (the cap is at a fixed CNode slot derived
/// from the index); the facade threads the kernel handle through because the
/// host has no implicit cap space — that is the ONLY shape difference, and it is
/// hidden inside the facade, never in PD code.
#[derive(Clone)]
pub struct Channel {
    index: usize,
    kernel: EmulatedKernel,
    table: Arc<ChannelTable>,
}

impl Channel {
    /// Construct a channel handle for `index` over the given kernel + table.
    /// (PD code receives this from the facade entry; it does not build it — on
    /// real Microkit a `Channel::new(index)` is a bare index. The boot harness
    /// hands each PD its kernel-bound channels.)
    pub fn bound(index: usize, kernel: EmulatedKernel, table: Arc<ChannelTable>) -> Self {
        Channel { index, kernel, table }
    }

    /// The channel index (mirrors `sel4_microkit::Channel::index`).
    pub fn index(&self) -> usize {
        self.index
    }

    /// `seL4_Signal` on the channel's Notification — the non-blocking
    /// `Channel::notify`. ORs THIS channel's index-bit into the receiver's
    /// notification badge and wakes it, so the receiver's `notified(channels)`
    /// recovers this channel (the Microkit badge-as-channel encoding).
    pub fn notify(&self) {
        if let Some(w) = self.table.get(self.index) {
            // The badge carries the channel index bit — the scope discriminator
            // Microkit puts in the notification badge.
            let _ = self.kernel.signal(w.notification, 1 << self.index);
        }
    }

    /// `seL4_Call` on the channel's Endpoint — the SYNCHRONOUS
    /// `Channel::pp_call`. Blocks until the server PD replies, returning the
    /// reply tag. (Requires the channel to be a PP channel — wired with an
    /// endpoint.) `payload` is the inline message bytes the call carries.
    pub fn pp_call(&self, msg_info: MessageInfo, payload: &[u8]) -> Result<(MessageInfo, Vec<u8>), IpcError> {
        let w = self.table.get(self.index).ok_or(IpcError::NoSuchObject)?;
        let ep = w.endpoint.ok_or(IpcError::NoSuchObject)?;
        let reply = self.kernel.call(ep, Message::new(msg_info.label(), payload.to_vec()))?;
        Ok((MessageInfo::new(reply.label, reply.bytes.len()), reply.bytes))
    }

    /// `seL4_IRQHandler_Ack` — the host has no real IRQ line, so this is a
    /// faithful no-op stub (an emulated device PD's `irq_ack` after servicing a
    /// synthetic interrupt). Kept so device-PD code that acks IRQs compiles
    /// unchanged on the semihost.
    pub fn irq_ack(&self) -> Result<(), IpcError> {
        Ok(())
    }
}

/// The application-specific part of a PD's main loop — the facade's [`Handler`],
/// mirroring `sel4_microkit::Handler` (`handler.rs`) name-for-name. **A PD impls
/// this trait with the SAME bodies on the semihost and on real seL4.**
pub trait Handler {
    /// A notification arrived on one or more channels. The default panics, as on
    /// real Microkit. `channels` is the badge-decoded set of channels that fired.
    fn notified(&mut self, channels: ChannelSet) {
        panic!("unexpected notification from channels {:?}", channels);
    }

    /// A protected-procedure call arrived on `channel`; return the reply tag.
    /// The default panics, as on real Microkit. `payload` is the call's inline
    /// bytes; write the reply into `reply_out` and return its tag.
    fn protected(&mut self, channel: usize, msg_info: MessageInfo, payload: &[u8], reply_out: &mut Vec<u8>) -> MessageInfo {
        let _ = (channel, msg_info, payload, reply_out);
        panic!("unexpected protected procedure call from channel {channel}");
    }

    /// A child PD faulted. The default panics, as on real Microkit.
    fn fault(&mut self, child: usize, msg_info: MessageInfo) -> Option<MessageInfo> {
        let _ = msg_info;
        panic!("unexpected fault from protection domain {child}");
    }
}

/// A `Handler` that overrides nothing — the facade's `NullHandler`. A PD that
/// only prints at `init()` and then idles (like `m0-hello`) returns this.
pub struct NullHandler;
impl Handler for NullHandler {}

/// What a PD's event loop should block on next — the channels it expects to be
/// `notified` on. The facade's loop waits on these notifications and dispatches
/// `Handler::notified` exactly as Microkit's `run()` blocks on `seL4_Recv` and
/// dispatches by event. (PP-server dispatch is driven separately via the
/// endpoint `recv`; this boot slice exercises the notification path, the §3
/// `Notified` event for the 2-PD notify slice.)
pub struct EventLoop {
    kernel: EmulatedKernel,
    /// The Notifications this PD waits on, paired with the channel-index badge
    /// each carries, so a wake decodes to a [`ChannelSet`].
    notifications: Vec<ObjectId>,
}

impl EventLoop {
    /// Build an event loop that waits on the given channel notifications.
    pub fn new(kernel: EmulatedKernel, notifications: Vec<ObjectId>) -> Self {
        EventLoop { kernel, notifications }
    }

    /// Run ONE dispatch step: block until any awaited notification fires, then
    /// call `handler.notified` with the decoded channel set. Returns `false`
    /// only if there are no notifications to wait on (a PD that idles forever,
    /// like `m0-hello` — the harness joins it by other means). This is the
    /// faithful Microkit loop body (`Handler::run`'s `recv` → dispatch), one
    /// step at a time so a boot test can bound it.
    pub fn step(&self, handler: &mut dyn Handler) -> bool {
        if self.notifications.is_empty() {
            return false;
        }
        // Block on the FIRST notification (the boot slice wires one per waiting
        // PD); a multi-notification PD would select across them. The kernel
        // `wait` blocks until the badge is non-zero and returns it.
        let badge = match self.kernel.wait(self.notifications[0]) {
            Ok(b) => b,
            Err(_) => return false,
        };
        handler.notified(ChannelSet(badge));
        true
    }
}

/// A protection domain running on the semihost — the facade's
/// `#[protection_domain]` entry, realized as a host thread.
///
/// `docs/DREGG-DESKTOP-OS.md §3`: a PD's `init()` returns its [`Handler`]; the
/// runtime then enters the event loop. On real Microkit the `#[protection_domain]`
/// macro wires `init` as the PD entry and the runtime calls `Handler::run`. On
/// the semihost [`ProtectionDomain::spawn`] does the same: it spawns a host
/// thread that runs `init`, then pumps the [`EventLoop`] — so **the PD body is
/// the same text; only the launch mechanism (a thread vs. an seL4 PD) differs.**
pub struct ProtectionDomain;

impl ProtectionDomain {
    /// Spawn a PD on its own host thread. `init` runs the PD's `init()` body
    /// (returning its handler) and is handed the kernel-bound channels; the
    /// thread then runs the PD's event loop until `steps` dispatches complete
    /// (a bounded boot test) or, for an idle PD (no notifications), returns
    /// immediately after `init`. Returns a [`JoinHandle`] the harness joins.
    ///
    /// This is the faithful seL4 boot shape: each PD is an independent schedulable
    /// entity (a thread here, a real PD there) that runs `init` once and then
    /// services events. The PDs share ONE [`EmulatedKernel`], so a `notify`/
    /// `pp_call` in one reaches the SAME endpoint/notification object in another.
    pub fn spawn<H, F>(name: impl Into<String>, init: F, steps: usize) -> JoinHandle<()>
    where
        H: Handler + 'static,
        F: FnOnce() -> (H, EventLoop) + Send + 'static,
    {
        let name = name.into();
        thread::Builder::new()
            .name(name)
            .spawn(move || {
                let (mut handler, evloop) = init();
                for _ in 0..steps {
                    if !evloop.step(&mut handler) {
                        break;
                    }
                }
            })
            .expect("spawn PD thread")
    }
}

/// The `memory_region_symbol!`-style shared-memory accessor — a PD's view onto a
/// shared region the firmament mapped into it at boot (`docs/DREGG-DESKTOP-OS.md
/// §3`: "`memory_region_symbol!` maps to host shared buffers").
///
/// On real Microkit `memory_region_symbol!(foo: *mut [u8], n = N)` resolves a
/// linker symbol the loader patched with the region's vaddr, giving the PD a
/// `*mut [u8]` it writes directly (its MMU mapping confines it). On the semihost
/// the region is a kernel-held host buffer ([`EmulatedKernel::create_region`]),
/// and [`Region`] is the PD's handle onto it; `with_mut` gives the
/// `thread: &mut [u8]` access the spec names.
///
/// **The labeled fidelity gap (§3, NOT laundered):** at v0 the region is in the
/// shared host address space, so a malicious PD-thread could reach it without
/// going through this handle — "no ambient authority" is by-construction-in-the-
/// API here, not MMU-enforced. The v1 process-backed upgrade (`shm_open`/`mmap`)
/// closes it. See [`EmulatedKernel::ISOLATION_FIDELITY`].
#[derive(Clone)]
pub struct Region {
    kernel: EmulatedKernel,
    id: ObjectId,
}

impl Region {
    /// A PD's handle onto the shared region with the given kernel object id.
    pub fn bound(kernel: EmulatedKernel, id: ObjectId) -> Self {
        Region { kernel, id }
    }

    /// The region's length in bytes (the `n` of `memory_region_symbol!`).
    pub fn len(&self) -> usize {
        self.kernel.region_len(self.id).unwrap_or(0)
    }

    /// Is the region empty?
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Mutate the region in place — the `thread: &mut [u8]` access of §3. PDs
    /// sharing the region see each other's writes (the net-client's
    /// smoltcp-over-shared-ring-buffer code runs against this unchanged).
    pub fn with_mut<T>(&self, f: impl FnOnce(&mut [u8]) -> T) -> T {
        self.kernel
            .region_with_mut(self.id, f)
            .expect("region exists")
    }

    /// Read a snapshot copy of the region's bytes.
    pub fn read(&self) -> Vec<u8> {
        self.kernel.region_read(self.id).unwrap_or_default()
    }
}

/// The semihost analog of `memory_region_symbol!` — resolve a PD's [`Region`]
/// handle onto a shared buffer.
///
/// On real Microkit the macro expands to a linker-symbol lookup. On the semihost
/// it expands to a [`Region::bound`] over the kernel object the firmament wired
/// for this PD. The PD writes the SAME call shape; the facade resolves it to the
/// host buffer. (We keep it a macro so the PD's source line matches the real one
/// modulo the backing; the boot harness pre-creates the region and binds it.)
#[macro_export]
macro_rules! memory_region_symbol {
    ($kernel:expr, $id:expr) => {{
        $crate::microkit_facade::Region::bound($kernel.clone(), $id)
    }};
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn channelset_decodes_badge_to_channels() {
        let cs = ChannelSet(0b1010);
        assert!(cs.contains(1));
        assert!(cs.contains(3));
        assert!(!cs.contains(0));
        let got: Vec<usize> = cs.iter().collect();
        assert_eq!(got, vec![1, 3]);
    }

    #[test]
    fn channel_notify_signals_the_wired_notification() {
        let k = EmulatedKernel::new();
        let notif = k.create_notification();
        let mut table = ChannelTable::new();
        table.wire(2, ChannelWiring { notification: notif, endpoint: None });
        let table = Arc::new(table);

        let ch = Channel::bound(2, k.clone(), table);
        ch.notify();
        // The wired notification carries channel 2's index bit (1 << 2).
        let badge = k.poll_notification(notif).unwrap();
        assert_eq!(badge, 1 << 2);
    }

    #[test]
    fn channel_pp_call_round_trips_through_the_endpoint() {
        // A client PD's `Channel::pp_call` (the SAME verb a real PD calls) blocks
        // until a server PD replies — the synchronous protected-procedure path,
        // backed by the kernel Endpoint. We run the server on a second thread
        // (a real PD's `protected` entry on its own thread) that Recvs, +1's the
        // label, doubles the first byte, and Replies.
        use crate::emulated_kernel::Message;
        use std::thread;

        let k = EmulatedKernel::new();
        let ep = k.create_endpoint();
        let mut table = ChannelTable::new();
        table.wire(3, ChannelWiring { notification: k.create_notification(), endpoint: Some(ep) });
        let table = Arc::new(table);

        let k_srv = k.clone();
        let server = thread::spawn(move || {
            let (msg, token) = k_srv.recv(ep).unwrap();
            let mut reply = msg.bytes.clone();
            reply[0] = reply[0].wrapping_mul(2);
            k_srv.reply(token, Message::new(msg.label + 1, reply)).unwrap();
        });

        let ch = Channel::bound(3, k.clone(), table);
        let (reply_tag, reply_bytes) = ch
            .pp_call(MessageInfo::new(10, 3), &[5u8, 0, 0])
            .expect("pp_call round-trips");
        server.join().unwrap();
        assert_eq!(reply_tag.label(), 11); // server +1'd the label
        assert_eq!(reply_bytes[0], 10); // 5 * 2 — the rendezvous round-tripped
    }

    #[test]
    fn region_handle_round_trips_shared_bytes() {
        let k = EmulatedKernel::new();
        let r = k.create_region(4);
        let region = memory_region_symbol!(k, r);
        region.with_mut(|b| b[1] = 0x5A);
        assert_eq!(region.read()[1], 0x5A);
        assert_eq!(region.len(), 4);
    }
}
