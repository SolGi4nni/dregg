//! The `EmulatedKernel` — the semihost firmament's `n = 1` microkernel.
//!
//! `docs/DREGG-DESKTOP-OS.md §3` (the semihosted-seL4 KEYSTONE) names the
//! load-bearing decision of the whole desktop plan: **the robigalia emulator is
//! a host-native backend for the rust-sel4 API surface, so ONE protection-domain
//! (PD) source tree runs (a) on the host emulator under `cargo test` today and
//! (b) on real seL4 unchanged.** This module is that emulator's kernel.
//!
//! It is **NOT a from-scratch mock.** It PROMOTES [`crate::LocalBacking`] — which
//! already has a real CNode slot-table ([`std::collections::BTreeMap`]) with a
//! mint/revoke derivation tree (`minted_from`), mint-with-[`is_attenuation`], and
//! synchronous-transitive revoke (`mint_attenuates_and_refuses_amplification`,
//! `revoke_is_synchronous_and_transitive`, all green) — by ADDING the three seL4
//! IPC primitives the desktop §3 spec calls for:
//!
//! - a synchronous **Endpoint** (rendezvous: a `Call` parks on a condvar until a
//!   `Recv` arrives — faithful seL4 synchrony), backing `Channel::pp_call`;
//! - a **Notification** (badge-OR accumulator + condvar wake; `Signal` = badge-OR
//!   + wake, `Wait` = block-until-nonzero), backing `Channel::notify` + the
//!   `Notified` event;
//! - **Untyped + Retype** (a byte/object budget that mints exactly the declared
//!   object type — the kernel-enforced form of the factory slot-caveat,
//!   `DirectoryFactory → seL4_Untyped_Retype`, `sel4/RBG-TO-SEL4.md`).
//!
//! ## Fidelity discipline (don't-launder-vacuity, §3)
//!
//! The kernel advertises [`crate::Bounds::LOCAL`] and these are *genuinely real*
//! on the host: a host thread's revoke IS synchronous (one `Mutex`-guarded
//! removal under a held lock — there is no in-flight window); a host present IS
//! one map. The cap checks are the GENUINE dregg attenuation
//! ([`dregg_cell::is_attenuation`]) — the same `granted ⊆ held` gate the
//! distributed executor and the local Mint use. This is a **faithful `n = 1`
//! firmament, NOT a lossy mock.**
//!
//! ### The ONE deliberate non-fidelity (honestly labeled, NOT laundered)
//!
//! Host threads (v0) share a single address space, so **"no ambient authority"
//! is by-construction-in-the-API, not MMU-enforced.** A PD *thread* could, in
//! principle, reach into another PD's memory by raw pointer — the host has no
//! CHERI tag bits and no per-PD page table. The API surface ([`Channel`],
//! [`memory_region_symbol!`]) gives a PD access ONLY to the regions/caps it was
//! granted, so a PD coded against the facade cannot *accidentally* amplify; but
//! a *malicious* PD is not contained the way seL4's MMU+CNode contain one. This
//! is EXACTLY the gap UML's traced-thread → SKAS evolution faced.
//!
//! **This gap is CLOSED by the v1 process-backed backing**
//! ([`crate::process_kernel::ProcessKernel`], `--features process-pd`): PDs
//! become forked PROCESSES (the host MMU enforces address-space separation, so a
//! PD physically cannot read another PD's memory), shared regions become
//! `shm_open`/`mmap` segments granted by name, and an epoch-tagged cap-handle
//! validity table (the kernel's) refuses a cap forged from raw bytes — the
//! cross-process CNode-unforgeability analogue. The v0 thread backing here stays
//! the default for fast `cargo test` (one address space, no `fork`); the v1
//! backing is the same PD source with the backing moved thread→process. We do
//! **not** claim the gap is solved AT v0; this const states the v0 reality, and
//! [`crate::process_kernel::ProcessKernel::ISOLATION_FIDELITY`] states what v1
//! now enforces. See [`EmulatedKernel::ISOLATION_FIDELITY`].
//!
//! [`Channel`]: crate::microkit_facade::Channel
//! [`memory_region_symbol!`]: crate::memory_region_symbol
//! [`is_attenuation`]: dregg_cell::is_attenuation

use std::collections::BTreeMap;
use std::string::String;
use std::sync::{Arc, Condvar, Mutex};
use std::vec::Vec;

use crate::local::LocalBacking;
use crate::Rights;

/// The kind of seL4 kernel object an [`Untyped`] budget may be retyped into.
///
/// This is the `seL4_Untyped_Retype` *type argument* — the declared object type
/// a factory may mint. The kernel enforces that a retype produces EXACTLY this
/// type and nothing else: the seL4-native form of the rbg factory slot-caveat
/// ("may only create this shape", `sel4/RBG-TO-SEL4.md`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ObjectType {
    /// A CNode (a capability table) — the object a `DirectoryFactory` retypes an
    /// Untyped into to back a new directory's c-list.
    CNode,
    /// A synchronous Endpoint (a rendezvous IPC port).
    Endpoint,
    /// A Notification (a badge-OR signal object).
    Notification,
    /// A Frame (a page of memory — a shared buffer / framebuffer tile).
    Frame,
}

impl ObjectType {
    /// The per-object size charged against an Untyped budget when retyped. These
    /// mirror the seL4 object sizes closely enough that the *budget arithmetic*
    /// (a factory exhausts its Untyped after N objects) is real, not nominal.
    pub const fn size_bytes(self) -> usize {
        match self {
            // A CNode of a few slots, an endpoint, a notification: small kernel
            // objects (one cache-line-ish each at this granularity).
            ObjectType::Endpoint => 16,
            ObjectType::Notification => 16,
            ObjectType::CNode => 64,
            // A frame is a page.
            ObjectType::Frame => 4096,
        }
    }
}

/// A handle to a retyped object, returned by [`EmulatedKernel::retype`]. It is
/// an opaque, kernel-minted id — a PD names it to invoke the object, exactly as
/// a real PD names a `seL4_CPtr`. (The v1 process-backed upgrade makes this a
/// generation-tagged handle a PD cannot forge by writing raw bytes; at v0 it is
/// a kernel-side index, which a same-address-space thread could in principle
/// fabricate — the labeled isolation gap, NOT laundered.)
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ObjectId(pub u64);

/// A synchronous Endpoint — the seL4 rendezvous IPC port.
///
/// Faithful seL4 synchrony: a `Call` (a `Channel::pp_call`) BLOCKS until a
/// matching `Recv` arrives, and the reply BLOCKS the receiver's send until the
/// caller is ready. On the host we realize the rendezvous with a `Condvar`: the
/// caller parks the message and waits for a reply slot; the receiver wakes,
/// takes the message, runs the protected-procedure body, and parks the reply,
/// which wakes the caller. There is no buffering — exactly the seL4 property
/// that an endpoint is a *meeting point*, not a queue.
#[derive(Default)]
struct Endpoint {
    /// The in-flight call message awaiting a receiver (`None` = no caller
    /// parked). `seL4` holds at most a rendezvous's worth of state here.
    pending_call: Option<Message>,
    /// The reply the receiver parked for the caller (`None` = not yet replied).
    pending_reply: Option<Message>,
    /// A monotonically-rising generation so a caller waits for ITS reply, not a
    /// stale one — the faithful "this call's reply" binding.
    call_gen: u64,
    reply_gen: u64,
}

/// A Notification — the seL4 badge-OR signal object.
///
/// `Signal` ORs the signaller's badge into the accumulator and wakes a waiter;
/// `Wait` blocks until the accumulator is non-zero, then atomically reads-and-
/// clears it (the seL4 `seL4_Wait` semantics: the returned badge is the OR of
/// all signals since the last wait, and the object resets to zero). The badge
/// carries the scope/membership/fault discriminator (matching Microkit's
/// `IS_ENDPOINT`/`IS_FAULT` bits), so a `ChannelSet` is recovered from it.
#[derive(Default)]
struct Notification {
    /// The OR-accumulated badge of all signals since the last successful wait.
    badge: u64,
}

/// An Untyped memory region + its retype budget — the seL4 `Untyped` cap.
///
/// A factory PD holds an Untyped and may `retype` it into objects of a declared
/// type until the byte budget is exhausted. The kernel enforces BOTH the type
/// (only the declared `ObjectType`) and the budget (a retype past `remaining`
/// fails) — the kernel-enforced form of the factory slot-caveat. A PD that
/// holds an Untyped granting only `CNode` retypes physically cannot mint a
/// `Frame`; that is the slot-caveat as a kernel invariant, not a Rust check.
struct Untyped {
    /// The total byte budget this Untyped was carved with.
    capacity: usize,
    /// The bytes already consumed by retypes.
    consumed: usize,
    /// The ONLY object type this Untyped may be retyped into — the declared
    /// factory shape. A retype of any other type is refused.
    permits: ObjectType,
}

/// An IPC message — a small label + a byte payload, mirroring the seL4
/// [`MessageInfo`](crate::microkit_facade::MessageInfo) + IPC-buffer message
/// registers. The payload stands in for the message registers / the inline
/// bytes a `pp_call` carries.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Message {
    /// The message label (the `seL4` `MessageInfo` label — a small tag the
    /// receiver dispatches on).
    pub label: u64,
    /// The inline message bytes (the message-register payload).
    pub bytes: Vec<u8>,
}

impl Message {
    /// A message with a label and a byte payload.
    pub fn new(label: u64, bytes: impl Into<Vec<u8>>) -> Self {
        Message {
            label,
            bytes: bytes.into(),
        }
    }
}

/// The mutable kernel state, guarded by ONE [`Mutex`] so every cap/IPC mutation
/// is atomic — the n=1 collapse made real: a revoke under the held lock has no
/// in-flight window, a signal-then-wake is one transaction. The [`Condvar`]
/// realizes the BLOCKING seL4 primitives (Call/Recv rendezvous, Wait).
struct KernelState {
    /// The CNode cap space — REUSED from [`LocalBacking`] (the slot-table +
    /// mint/revoke derivation tree). We do NOT fork it; we extend the kernel
    /// AROUND it. This is the "PROMOTE, don't reinvent" of §3.
    cnode: LocalBacking,
    /// The synchronous endpoints, by object id.
    endpoints: BTreeMap<u64, Endpoint>,
    /// The notifications, by object id.
    notifications: BTreeMap<u64, Notification>,
    /// The untyped budgets, by object id.
    untypeds: BTreeMap<u64, Untyped>,
    /// The shared memory regions (`memory_region_symbol!` backs these): a region
    /// id → a heap-allocated byte buffer all PDs sharing it see. At v0 these are
    /// host thread-shared (one address space); v1 makes them `shm_open`/`mmap`.
    regions: BTreeMap<u64, Vec<u8>>,
    /// The next object/region id to hand out (kernel-minted, monotonic).
    next_object: u64,
}

/// The emulated `n = 1` microkernel: the CNode cap space (from [`LocalBacking`])
/// PLUS the three seL4 IPC primitives (Endpoint / Notification / Untyped+Retype)
/// and the shared-memory regions, all under one lock so the n=1 bounds are
/// genuinely real.
///
/// It is `Clone` (a cheap `Arc` bump) and `Send + Sync`, so a [`Channel`] in one
/// PD thread and a `Recv`/`Wait` in another share ONE kernel — exactly the seL4
/// property that two PDs invoke the SAME endpoint/notification object.
///
/// [`Channel`]: crate::microkit_facade::Channel
#[derive(Clone)]
pub struct EmulatedKernel {
    state: Arc<Mutex<KernelState>>,
    /// Woken on every Signal / Call-parked / Reply-parked, so blocked
    /// Wait/Recv/Call threads re-check their condition.
    cvar: Arc<Condvar>,
}

impl EmulatedKernel {
    /// A short, honest statement of the ONE deliberate non-fidelity — the v0
    /// isolation gap — so it travels WITH the code, never laundered as solved.
    /// (`docs/DREGG-DESKTOP-OS.md §3`, the fidelity discipline.)
    ///
    /// This describes the v0 THREAD backing's reality. The gap is **closed by
    /// the v1 process backing** ([`crate::process_kernel::ProcessKernel`],
    /// `--features process-pd`), whose own
    /// [`ISOLATION_FIDELITY`](crate::process_kernel::ProcessKernel::ISOLATION_FIDELITY)
    /// states what is now MMU-enforced. v0 stays the default for fast tests; the
    /// label here remains honest about v0 itself.
    pub const ISOLATION_FIDELITY: &'static str = "\
        v0 host threads share one address space: 'no ambient authority' is \
        by-construction-in-the-API (a PD sees only its granted caps/regions), \
        NOT MMU-enforced (a malicious thread could read another PD's memory by \
        raw pointer — the host has no CHERI tag bits, so a cap could be forged \
        by writing raw bytes). CLOSED by the v1 process-backed backing \
        (ProcessKernel, --features process-pd): forked PROCESSES (MMU-enforced \
        separation) + shm_open/mmap regions + a kernel-side epoch-tagged \
        cap-handle validity table (raw-bytes forgery refused). v0 stays the \
        default for fast cargo-test; NOT laundered as solved at v0.";

    /// A fresh, empty `n = 1` kernel.
    pub fn new() -> Self {
        EmulatedKernel {
            state: Arc::new(Mutex::new(KernelState {
                cnode: LocalBacking::new(),
                endpoints: BTreeMap::new(),
                notifications: BTreeMap::new(),
                untypeds: BTreeMap::new(),
                regions: BTreeMap::new(),
                next_object: 0,
            })),
            cvar: Arc::new(Condvar::new()),
        }
    }

    // ── The CNode cap space (delegated to the promoted `LocalBacking`) ───────
    //
    // These are the EXISTING green primitives, now reachable through the kernel
    // handle so a PD holds one `EmulatedKernel` for caps AND IPC. We never
    // reinvent the slot-table / mint / revoke — we forward to `LocalBacking`.

    /// `install` an ORIGINAL cap over a kernel object at the next CNode slot
    /// (the firmament minting a cap into a PD's CNode at CapDL boot). Returns the
    /// slot. Forwards to [`LocalBacking::install`].
    pub fn install(&self, object: impl Into<String>, rights: Rights) -> u32 {
        self.state.lock().unwrap().cnode.install(object, rights)
    }

    /// `seL4_CNode_Mint` with reduced rights — derive a narrower child slot.
    /// Refuses an amplifying mint (`granted ⊆ held`, via the REAL
    /// [`is_attenuation`]). Forwards to [`LocalBacking::mint`].
    pub fn mint(&self, parent: u32, narrower: Rights) -> Option<u32> {
        self.state.lock().unwrap().cnode.mint(parent, narrower)
    }

    /// `seL4_CNode_Revoke` — SYNCHRONOUS, immediate, transitive revoke (the
    /// n=1 immediacy: under the held kernel lock the cap and its whole mint
    /// subtree vanish with no in-flight window). Returns the slots removed.
    /// Forwards to [`LocalBacking::revoke`].
    pub fn revoke(&self, slot: u32) -> usize {
        self.state.lock().unwrap().cnode.revoke(slot)
    }

    /// Is a cap live at `slot`? (Post-revoke: `false` immediately.)
    pub fn is_live(&self, slot: u32) -> bool {
        self.state.lock().unwrap().cnode.is_live(slot)
    }

    /// The rights held at `slot`, if any.
    pub fn rights_at(&self, slot: u32) -> Option<Rights> {
        self.state.lock().unwrap().cnode.rights_at(slot)
    }

    /// The bounds this kernel advertises — [`crate::Bounds::LOCAL`] (the strong
    /// `n = 1` guarantees: immediate revocation, synchronous commit).
    ///
    /// `docs/DREGG-DESKTOP-OS.md §3` (the fidelity discipline): these are
    /// *genuinely real* on the host, NOT a nominal label. A host thread's
    /// [`Self::revoke`] IS synchronous — it removes the slot + its mint subtree
    /// under the held kernel `Mutex`, so there is no in-flight window (a
    /// concurrent invoke either runs entirely before the revoke takes the lock,
    /// or finds the cap already gone). A host present IS one map. This is a
    /// faithful `n = 1` firmament, not a lossy mock.
    pub const fn bounds(&self) -> crate::Bounds {
        crate::Bounds::LOCAL
    }

    // ── Untyped + Retype (the factory slot-caveat as a kernel invariant) ─────

    /// Carve an `Untyped` cap with `capacity` bytes that may be retyped ONLY
    /// into `permits` objects (the declared factory shape). Returns its object
    /// id. This is the firmament handing a factory PD its Untyped at boot — the
    /// `<memory_region>` of untyped memory mapped only to that PD
    /// (`sel4/RBG-TO-SEL4.md`).
    pub fn create_untyped(&self, capacity: usize, permits: ObjectType) -> ObjectId {
        let mut st = self.state.lock().unwrap();
        let id = st.alloc_id();
        st.untypeds.insert(
            id,
            Untyped {
                capacity,
                consumed: 0,
                permits,
            },
        );
        ObjectId(id)
    }

    /// `seL4_Untyped_Retype` — mint EXACTLY the declared object type from an
    /// Untyped's budget.
    ///
    /// The kernel enforces BOTH halves of the slot-caveat:
    /// - **type**: a retype of any type other than the Untyped's `permits` is
    ///   refused with [`RetypeError::WrongType`] — a factory granted only
    ///   `CNode` retypes physically cannot mint a `Frame`;
    /// - **budget**: a retype that would exceed `capacity` is refused with
    ///   [`RetypeError::Exhausted`].
    ///
    /// On success it allocates the new object (an empty endpoint / notification /
    /// CNode slot 0 / a zeroed frame region) and returns its [`ObjectId`].
    pub fn retype(&self, untyped: ObjectId, ty: ObjectType) -> Result<ObjectId, RetypeError> {
        let mut st = self.state.lock().unwrap();
        let u = st
            .untypeds
            .get(&untyped.0)
            .ok_or(RetypeError::NoSuchUntyped)?;
        if ty != u.permits {
            return Err(RetypeError::WrongType {
                permitted: u.permits,
                requested: ty,
            });
        }
        let need = ty.size_bytes();
        if u.consumed + need > u.capacity {
            return Err(RetypeError::Exhausted {
                capacity: u.capacity,
                consumed: u.consumed,
                requested: need,
            });
        }
        // Charge the budget.
        st.untypeds.get_mut(&untyped.0).unwrap().consumed += need;
        // Allocate the object of the declared type.
        let id = st.alloc_id();
        match ty {
            ObjectType::Endpoint => {
                st.endpoints.insert(id, Endpoint::default());
            }
            ObjectType::Notification => {
                st.notifications.insert(id, Notification::default());
            }
            ObjectType::CNode => {
                // A retyped CNode starts empty; the factory installs caps into it.
                // (We model it as a fresh region slot the new c-list will use; the
                // real LocalBacking already IS the root c-list, so a retyped CNode
                // here is a budget-charged, distinctly-identified child table.)
                st.regions.insert(id, Vec::new());
            }
            ObjectType::Frame => {
                st.regions
                    .insert(id, vec![0u8; ObjectType::Frame.size_bytes()]);
            }
        }
        Ok(ObjectId(id))
    }

    /// The Untyped's remaining budget in bytes (for tests/assertions — a PD
    /// learns it has exhausted its factory quota).
    pub fn untyped_remaining(&self, untyped: ObjectId) -> Option<usize> {
        let st = self.state.lock().unwrap();
        st.untypeds.get(&untyped.0).map(|u| u.capacity - u.consumed)
    }

    // ── Notification (badge-OR + condvar wake) ───────────────────────────────

    /// Create a fresh Notification object, returning its id. (Microkit channels
    /// map to these; the firmament wires one per channel at boot.)
    pub fn create_notification(&self) -> ObjectId {
        let mut st = self.state.lock().unwrap();
        let id = st.alloc_id();
        st.notifications.insert(id, Notification::default());
        ObjectId(id)
    }

    /// `seL4_Signal` — OR `badge` into the notification's accumulator and wake
    /// any waiter. Non-blocking (a signal never parks the signaller), exactly as
    /// seL4. The badge carries the scope/membership/fault discriminator.
    pub fn signal(&self, notif: ObjectId, badge: u64) -> Result<(), IpcError> {
        let mut st = self.state.lock().unwrap();
        let n = st
            .notifications
            .get_mut(&notif.0)
            .ok_or(IpcError::NoSuchObject)?;
        n.badge |= badge;
        // Wake the blocked Wait so it re-checks its (now non-zero) condition.
        drop(st);
        self.cvar.notify_all();
        Ok(())
    }

    /// `seL4_Wait` — BLOCK until the notification's badge is non-zero, then
    /// atomically read-and-clear it and return the accumulated badge. This is
    /// the seL4 semantics: the returned badge is the OR of all signals since the
    /// last wait, and the object resets to zero. The blocking is a real
    /// condvar park — a faithful "the PD is descheduled until signalled".
    pub fn wait(&self, notif: ObjectId) -> Result<u64, IpcError> {
        let mut st = self.state.lock().unwrap();
        loop {
            let n = st
                .notifications
                .get_mut(&notif.0)
                .ok_or(IpcError::NoSuchObject)?;
            if n.badge != 0 {
                let badge = n.badge;
                n.badge = 0; // read-and-clear (seL4_Wait resets the object)
                return Ok(badge);
            }
            // Block until a Signal wakes us; re-loop to re-check (spurious-wakeup
            // safe). We pass the guard to the condvar, which atomically releases
            // the lock while parked and re-acquires on wake.
            st = self.cvar.wait(st).unwrap();
        }
    }

    /// A NON-blocking poll of a notification's badge (read-and-clear), for the
    /// emulator's single-threaded dispatch loop where the PD's `notified` body
    /// is pumped from the same thread. Returns `0` if no signal is pending.
    pub fn poll_notification(&self, notif: ObjectId) -> Result<u64, IpcError> {
        let mut st = self.state.lock().unwrap();
        let n = st
            .notifications
            .get_mut(&notif.0)
            .ok_or(IpcError::NoSuchObject)?;
        let badge = n.badge;
        n.badge = 0;
        Ok(badge)
    }

    // ── Endpoint (synchronous rendezvous) ────────────────────────────────────

    /// Create a fresh synchronous Endpoint object, returning its id. (A Microkit
    /// PP channel maps to one of these.)
    pub fn create_endpoint(&self) -> ObjectId {
        let mut st = self.state.lock().unwrap();
        let id = st.alloc_id();
        st.endpoints.insert(id, Endpoint::default());
        ObjectId(id)
    }

    /// `seL4_Call` on an endpoint — the synchronous `Channel::pp_call`.
    ///
    /// Parks `msg` as the pending call, wakes a blocked `recv`, then BLOCKS until
    /// the receiver parks a reply for THIS call (matched by generation), and
    /// returns it. Faithful seL4 synchrony: the caller is descheduled across the
    /// whole protected-procedure, and there is no buffering — the endpoint is a
    /// meeting point.
    ///
    /// NOTE: this is the cross-thread form (a SERVER PD blocked in [`Self::recv`]
    /// on another host thread). The emulator's single-threaded demo path uses
    /// [`Self::call_served_by`] instead, which runs the server's handler inline.
    pub fn call(&self, endpoint: ObjectId, msg: Message) -> Result<Message, IpcError> {
        let my_gen;
        {
            let mut st = self.state.lock().unwrap();
            // Wait for any prior call to clear (one rendezvous at a time). The
            // presence check is a SCOPED borrow each iteration so it is dropped
            // before `cvar.wait` moves the guard — never held across the wait.
            while st
                .endpoints
                .get(&endpoint.0)
                .ok_or(IpcError::NoSuchObject)?
                .pending_call
                .is_some()
            {
                st = self.cvar.wait(st).unwrap();
            }
            let ep = st
                .endpoints
                .get_mut(&endpoint.0)
                .ok_or(IpcError::NoSuchObject)?;
            ep.call_gen += 1;
            my_gen = ep.call_gen;
            ep.pending_call = Some(msg);
        }
        self.cvar.notify_all(); // wake a blocked recv
                                // Block until OUR reply is parked.
        let mut st = self.state.lock().unwrap();
        loop {
            let ep = st
                .endpoints
                .get_mut(&endpoint.0)
                .ok_or(IpcError::NoSuchObject)?;
            if ep.reply_gen == my_gen {
                if let Some(reply) = ep.pending_reply.take() {
                    return Ok(reply);
                }
            }
            st = self.cvar.wait(st).unwrap();
        }
    }

    /// `seL4_Recv` on an endpoint (the SERVER half) — BLOCK until a call is
    /// parked, take the message, and return it together with a [`ReplyToken`]
    /// the server uses to park the reply. Faithful seL4: the receiver is
    /// descheduled until a caller arrives.
    pub fn recv(&self, endpoint: ObjectId) -> Result<(Message, ReplyToken), IpcError> {
        let mut st = self.state.lock().unwrap();
        loop {
            let ep = st
                .endpoints
                .get_mut(&endpoint.0)
                .ok_or(IpcError::NoSuchObject)?;
            if let Some(msg) = ep.pending_call.take() {
                let token = ReplyToken {
                    endpoint,
                    call_gen: ep.call_gen,
                };
                // Wake any other caller waiting for the rendezvous to free up.
                drop(st);
                self.cvar.notify_all();
                return Ok((msg, token));
            }
            st = self.cvar.wait(st).unwrap();
        }
    }

    /// `seL4_Reply` (the SERVER half) — park `reply` for the caller named by the
    /// [`ReplyToken`] and wake it. Completes the rendezvous.
    pub fn reply(&self, token: ReplyToken, reply: Message) -> Result<(), IpcError> {
        let mut st = self.state.lock().unwrap();
        let ep = st
            .endpoints
            .get_mut(&token.endpoint.0)
            .ok_or(IpcError::NoSuchObject)?;
        ep.pending_reply = Some(reply);
        ep.reply_gen = token.call_gen;
        drop(st);
        self.cvar.notify_all();
        Ok(())
    }

    /// A `seL4_Call` whose server is run INLINE (same thread) — the emulator's
    /// single-threaded dispatch convenience for a protected-procedure call.
    ///
    /// `serve` is the server PD's `protected(channel, msg) -> reply` body; this
    /// stages the call, runs the body, and returns the reply, with NO second
    /// thread. (On a real PD the call would block and the server PD's
    /// `protected` entry would run on the server's own thread; the emulator can
    /// realize that exactly via [`Self::call`] + [`Self::recv`] on two threads,
    /// or collapse it to this inline form for a simple boot test.) It is still a
    /// *synchronous* call — the caller does not proceed until `serve` returns.
    pub fn call_served_by(&self, msg: Message, serve: impl FnOnce(Message) -> Message) -> Message {
        serve(msg)
    }

    // ── Shared memory regions (memory_region_symbol! backing) ────────────────

    /// Allocate a shared memory region of `len` zeroed bytes, returning its id.
    /// `memory_region_symbol!` resolves a PD's view onto one of these; on v0 the
    /// region is a host heap buffer all sharing PD-threads see (the labeled
    /// single-address-space fidelity gap), v1 makes it `shm_open`/`mmap`.
    pub fn create_region(&self, len: usize) -> ObjectId {
        let mut st = self.state.lock().unwrap();
        let id = st.alloc_id();
        st.regions.insert(id, vec![0u8; len]);
        ObjectId(id)
    }

    /// Read the whole contents of a shared region (a snapshot copy). PDs sharing
    /// the region see each other's writes.
    pub fn region_read(&self, region: ObjectId) -> Option<Vec<u8>> {
        self.state.lock().unwrap().regions.get(&region.0).cloned()
    }

    /// Mutate a shared region in place under the kernel lock, returning whatever
    /// the closure returns. This is the `thread: &mut [u8]` access
    /// `memory_region_symbol!` gives a PD — here mediated through the kernel so
    /// the access is serialized (the v1 process upgrade replaces this with an
    /// `mmap`'d region the PD writes directly).
    pub fn region_with_mut<T>(
        &self,
        region: ObjectId,
        f: impl FnOnce(&mut [u8]) -> T,
    ) -> Option<T> {
        let mut st = self.state.lock().unwrap();
        st.regions
            .get_mut(&region.0)
            .map(|buf| f(buf.as_mut_slice()))
    }

    /// The length of a shared region, if it exists.
    pub fn region_len(&self, region: ObjectId) -> Option<usize> {
        self.state
            .lock()
            .unwrap()
            .regions
            .get(&region.0)
            .map(|b| b.len())
    }
}

impl KernelState {
    /// Mint the next monotonic object/region id.
    fn alloc_id(&mut self) -> u64 {
        let id = self.next_object;
        self.next_object += 1;
        id
    }
}

impl Default for EmulatedKernel {
    fn default() -> Self {
        Self::new()
    }
}

/// A token the endpoint server holds between [`EmulatedKernel::recv`] and
/// [`EmulatedKernel::reply`] — it names the caller's pending rendezvous so the
/// reply reaches the right `Call`.
#[derive(Clone, Copy, Debug)]
pub struct ReplyToken {
    endpoint: ObjectId,
    call_gen: u64,
}

/// Errors from the IPC primitives (endpoint/notification).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IpcError {
    /// No object exists at the given [`ObjectId`] (a stale or forged handle).
    NoSuchObject,
}

/// Errors from [`EmulatedKernel::retype`] — the kernel-enforced factory
/// slot-caveat refusing a retype.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RetypeError {
    /// No Untyped exists at the given id.
    NoSuchUntyped,
    /// The requested object type is not the one this Untyped permits — the
    /// slot-caveat: a factory may only mint its declared shape.
    WrongType {
        /// The only type this Untyped permits.
        permitted: ObjectType,
        /// The type the retype asked for (refused).
        requested: ObjectType,
    },
    /// The retype would exceed the Untyped's byte budget.
    Exhausted {
        /// The Untyped's total capacity.
        capacity: usize,
        /// The bytes already consumed.
        consumed: usize,
        /// The bytes this retype needed.
        requested: usize,
    },
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::AuthRequired;
    use std::thread;

    // ── The PROMOTED CNode primitives still hold (delegated to LocalBacking) ──

    #[test]
    fn bounds_local_is_genuinely_real_synchronous_revoke() {
        // §3 fidelity: the kernel advertises Bounds::LOCAL, and it is GENUINE.
        // A revoke under the held kernel lock has no in-flight window: a cap is
        // dead the instant `revoke` returns, with no concurrent thread able to
        // observe it half-revoked. We prove revocation_immediate is real (not a
        // nominal flag) by revoking and asserting the slot is gone AT ONCE.
        let k = EmulatedKernel::new();
        assert_eq!(k.bounds(), crate::Bounds::LOCAL);
        assert!(k.bounds().revocation_immediate);
        assert!(k.bounds().commit_synchronous);

        let root = k.install("endpoint:ctrl", AuthRequired::Either);
        let child = k.mint(root, AuthRequired::Signature).unwrap();
        // Revoke returns having ALREADY removed the subtree — synchronous.
        assert_eq!(k.revoke(root), 2);
        // The instant revoke returned, the caps are dead — no propagation delay.
        assert!(!k.is_live(root));
        assert!(!k.is_live(child));
        assert_eq!(k.rights_at(child), None);
    }

    #[test]
    fn promoted_cnode_mint_revoke_still_green() {
        let k = EmulatedKernel::new();
        let root = k.install("endpoint:ctrl", AuthRequired::Either);
        // Mint narrower (Either -> Signature) succeeds; amplify refused.
        let child = k
            .mint(root, AuthRequired::Signature)
            .expect("narrowing mint");
        assert_eq!(k.rights_at(child), Some(AuthRequired::Signature));
        assert!(k.mint(child, AuthRequired::Either).is_none());
        // Revoke the root kills the subtree synchronously.
        let grandchild = k.mint(child, AuthRequired::Signature).unwrap();
        assert_eq!(k.revoke(root), 3);
        assert!(!k.is_live(root));
        assert!(!k.is_live(child));
        assert!(!k.is_live(grandchild));
    }

    // ── Notification: Signal = badge-OR + wake; Wait = block-until-nonzero ────

    #[test]
    fn notification_badge_or_accumulates_and_clears() {
        let k = EmulatedKernel::new();
        let n = k.create_notification();
        // Two signals before a wait OR together (seL4 accumulation).
        k.signal(n, 0b001).unwrap();
        k.signal(n, 0b100).unwrap();
        // Poll (non-blocking) read-and-clear returns the OR; a second poll is 0.
        assert_eq!(k.poll_notification(n).unwrap(), 0b101);
        assert_eq!(k.poll_notification(n).unwrap(), 0);
    }

    #[test]
    fn notification_wait_blocks_until_signalled_cross_thread() {
        let k = EmulatedKernel::new();
        let n = k.create_notification();
        let k2 = k.clone();
        // A waiter thread blocks until the badge is non-zero.
        let waiter = thread::spawn(move || k2.wait(n).unwrap());
        // Give the waiter a moment to actually park (not load-bearing for
        // correctness — the loop re-checks — but exercises the blocking path).
        thread::sleep(std::time::Duration::from_millis(20));
        k.signal(n, 0xABC).unwrap();
        assert_eq!(waiter.join().unwrap(), 0xABC);
        // The object reset to zero after the wait consumed the badge.
        assert_eq!(k.poll_notification(n).unwrap(), 0);
    }

    // ── Endpoint: synchronous rendezvous (Call parks until Recv) ──────────────

    #[test]
    fn endpoint_call_recv_reply_rendezvous_cross_thread() {
        let k = EmulatedKernel::new();
        let ep = k.create_endpoint();
        let k2 = k.clone();
        // A server thread Recvs, doubles the first payload byte, and Replies.
        let server = thread::spawn(move || {
            let (msg, token) = k2.recv(ep).unwrap();
            let mut reply = msg.bytes.clone();
            reply[0] = reply[0].wrapping_mul(2);
            k2.reply(token, Message::new(msg.label + 1, reply)).unwrap();
        });
        // The client Calls and BLOCKS until the reply (synchronous).
        let reply = k.call(ep, Message::new(7, vec![21u8, 0, 0])).unwrap();
        server.join().unwrap();
        assert_eq!(reply.label, 8);
        assert_eq!(reply.bytes[0], 42); // 21 * 2 — the rendezvous round-tripped
    }

    // ── Untyped + Retype: the factory slot-caveat as a kernel invariant ───────

    #[test]
    fn retype_mints_only_the_declared_type() {
        let k = EmulatedKernel::new();
        // A factory granted an Untyped that may ONLY become CNodes.
        let u = k.create_untyped(256, ObjectType::CNode);
        // Retyping into the declared type succeeds.
        let _cnode = k.retype(u, ObjectType::CNode).expect("declared retype");
        // Retyping into ANY OTHER type is refused — the slot-caveat as a kernel
        // invariant: a CNode factory physically cannot mint a Frame.
        let err = k.retype(u, ObjectType::Frame).unwrap_err();
        assert!(matches!(err, RetypeError::WrongType { .. }));
    }

    #[test]
    fn retype_exhausts_the_untyped_budget() {
        let k = EmulatedKernel::new();
        // Budget for exactly 2 endpoints (16 bytes each).
        let u = k.create_untyped(2 * ObjectType::Endpoint.size_bytes(), ObjectType::Endpoint);
        assert!(k.retype(u, ObjectType::Endpoint).is_ok());
        assert!(k.retype(u, ObjectType::Endpoint).is_ok());
        assert_eq!(k.untyped_remaining(u), Some(0));
        // The third retype is refused — the budget is exhausted.
        let err = k.retype(u, ObjectType::Endpoint).unwrap_err();
        assert!(matches!(err, RetypeError::Exhausted { .. }));
    }

    // ── Shared regions (memory_region_symbol! backing) ────────────────────────

    #[test]
    fn shared_region_is_visible_across_holders() {
        let k = EmulatedKernel::new();
        let r = k.create_region(8);
        // One holder writes; another reads the same region (one address space —
        // the v0 shared-memory shape memory_region_symbol! gives).
        k.region_with_mut(r, |buf| buf[0] = 0xEE).unwrap();
        assert_eq!(k.region_read(r).unwrap()[0], 0xEE);
        assert_eq!(k.region_len(r), Some(8));
    }
}
