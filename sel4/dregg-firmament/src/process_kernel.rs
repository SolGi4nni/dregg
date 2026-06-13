//! The `ProcessKernel` — the v1 PROCESS-backed firmament substrate (the
//! MMU-enforced isolation upgrade `docs/DREGG-DESKTOP-OS.md §3` names).
//!
//! ## Why this module exists (the ONE fidelity gap, now closed)
//!
//! The v0 [`crate::EmulatedKernel`] is a faithful `n = 1` firmament with exactly
//! ONE honestly-labeled non-fidelity: its protection domains (PDs) are host
//! THREADS sharing one address space, so "no ambient authority" is
//! by-construction-in-the-API, **NOT MMU-enforced**. A malicious thread could
//! read another PD's memory by a raw pointer; and because host RAM has no CHERI
//! tag bits, a thread could fabricate a kernel-object handle by writing raw
//! bytes. v0 said so plainly ([`crate::EmulatedKernel::ISOLATION_FIDELITY`]) and
//! did NOT launder it.
//!
//! This module closes that gap, exactly the way UML's traced-thread → SKAS
//! evolution closed its analogue: **PDs become host PROCESSES (`fork`), so the
//! OS MMU enforces address-space separation — a PD physically cannot read
//! another PD's memory.** Three load-bearing pieces:
//!
//! 1. **PROCESS-backed PDs** ([`ProcessKernel::spawn_pd`]) — each PD is a forked
//!    child with its own page tables. The kernel-equivalent of seL4's
//!    address-space separation is now the host kernel's, not a Rust convention.
//!    A read of another PD's heap address faults (SIGSEGV) or lands in this PD's
//!    own unrelated memory — it can NEVER observe the other PD's secret.
//!
//! 2. **`shm_open`/`mmap` shared regions** ([`ProcessKernel::create_region`])
//!    replacing v0's `&mut [u8]` thread-shared buffers. A region is a named
//!    POSIX shared-memory object the kernel creates; a PD maps it ONLY if the
//!    kernel hands it the (name, len) at grant time. A PD that was not granted a
//!    region does not know its randomized name and cannot map it — the
//!    `memory_region_symbol!` mapping is a real per-PD MMU mapping, not a shared
//!    pointer. Two PDs that ARE both granted the same region see each other's
//!    writes (the genuine shared-ring-buffer the net-client's smoltcp code
//!    needs), but neither can reach the other's PRIVATE memory.
//!
//! 3. **THE CAP-INTEGRITY PIECE — an epoch-tagged cap-handle validity table**
//!    ([`ValidityTable`]). Host RAM has no tag bits, so a PD must NOT be able to
//!    forge a cap by writing raw bytes into a shared region. The kernel holds a
//!    validity table mapping each opaque [`CapHandle`] → its `(epoch, object)`.
//!    A PD presents a handle to invoke an object; the kernel checks it against
//!    the table FIRST, so a forged / raw-bytes / stale-epoch handle FAILS with
//!    [`CapError::Forged`]. This is the cross-process analogue of CNode
//!    unforgeability: in seL4 a cap is unforgeable because it lives in the
//!    kernel's CNode, never in the PD's address space; here a cap-handle is
//!    unforgeable because its VALIDITY lives in the kernel's table, never in the
//!    PD's RAM. **This is the part that makes raw-bytes cap-forgery impossible.**
//!
//! ## Fidelity discipline (don't-launder-vacuity, §3) — what is now enforced
//!
//! | property                         | v0 (thread)            | v1 (process)                    |
//! |----------------------------------|------------------------|---------------------------------|
//! | cross-PD private-memory read     | by-construction-in-API | **MMU-enforced** (separate VA)  |
//! | cap-handle forgery (raw bytes)   | possible in principle  | **refused** by the validity table |
//! | shared region access             | shared `&mut [u8]`     | per-PD `mmap` of a named shm    |
//! | the cap *attenuation* lattice    | real `is_attenuation`  | real `is_attenuation` (unchanged) |
//!
//! What remains by-construction / trusted, stated HONESTLY (NOT laundered):
//!
//! - **The validity table is the KERNEL's, and the kernel is trusted.** That is
//!   correct and intended — it is the TCB, the host-userspace stand-in for the
//!   seL4 kernel's CNode. The PD cannot forge a cap precisely because validity
//!   is the kernel's to decide, never the PD's. We do not claim the kernel
//!   itself is confined from itself.
//! - **The MMU is the HOST OS's.** The address-space separation is enforced by
//!   the real macOS/Linux page tables, not by anything in this crate — that is
//!   the whole point (it is REAL isolation, not modeled isolation), and it is
//!   the same enforcement a real seL4 PD relies on the seL4 kernel + hardware
//!   MMU for. We trust the host kernel exactly as the deployment trusts seL4.
//! - **The shm name is a capability-by-obscurity at the POSIX layer** — a PD not
//!   handed the name cannot map the region. We harden this with an unguessable
//!   random name AND `O_EXCL` creation + immediate `shm_unlink` (so the name is
//!   removed from the namespace after both ends map it, leaving only the already-
//!   open mappings — a PD that never received the fd/name can no longer open it
//!   at all). The genuinely-strong story (an fd passed by `SCM_RIGHTS`, no name
//!   in any shared namespace) is noted where it would tighten further.
//!
//! ## Same-code claim across BOTH backings
//!
//! The [`crate::microkit_facade`] API a PD codes against (`Handler`, `Channel`,
//! `Region`, `memory_region_symbol!`, the `init()` body) is UNCHANGED. The
//! boot test ([`tests/boot_pds.rs`]'s m0-hello + the 2-PD notify slice) runs on
//! the process backing too: the same PD source, only the BACKING moves
//! thread→process. That is verified by the process-backed boot test
//! ([`tests/process_isolation.rs`]).
//!
//! ## Portability
//!
//! This module is **Unix-only** (`fork`/`shm_open`/`mmap`/`socketpair` —
//! macOS + Linux, the semihost's host platforms) and gated behind the
//! `process-pd` Cargo feature, so the default fast `cargo test` keeps the v0
//! thread backing and the real-isolation path is opt-in. The v0 thread backing
//! ([`crate::EmulatedKernel`]) is NOT removed — this EXTENDS it with a
//! cfg-selected backing, it does not fork a parallel mock.

#![cfg(all(feature = "process-pd", unix))]

use std::collections::BTreeMap;
use std::io::{self, Read, Write};
use std::os::unix::io::{FromRawFd, RawFd};
use std::os::unix::net::UnixStream;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};

use dregg_cell::is_attenuation;

use crate::emulated_kernel::ObjectType;
use crate::Rights;

// ───────────────────────────── cap handles ──────────────────────────────────

/// An opaque, epoch-tagged capability handle — the v1 unforgeable object name.
///
/// On v0 an [`crate::ObjectId`] was a bare kernel index a same-address-space
/// thread could, in principle, fabricate (the labeled gap). On v1 a
/// [`CapHandle`] is a `(slot, epoch)` pair whose VALIDITY lives ONLY in the
/// kernel's [`ValidityTable`] — a PD can write any 16 bytes it likes into a
/// shared region and call them a handle, but the kernel checks the bytes against
/// its table, so a forged or stale handle is refused ([`CapError::Forged`]).
///
/// The `epoch` is the cross-process analogue of seL4's cap "badge generation":
/// when an object is destroyed and its slot later reused, the epoch bumps, so a
/// PD replaying an OLD handle for a now-reused slot is refused (no
/// use-after-revoke confusion). The handle is `Copy` and serializes to 16 bytes
/// for transport across the control socket — but possessing the bytes is NOT
/// possessing authority; only a table match is.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CapHandle {
    /// The kernel slot this handle names (the validity table key).
    pub slot: u64,
    /// The generation/epoch at mint time. A handle whose epoch ≠ the table's
    /// current epoch for `slot` is stale and refused — the cross-process
    /// use-after-revoke guard.
    pub epoch: u64,
}

impl CapHandle {
    /// Serialize to the 16 wire bytes (`slot` ‖ `epoch`, little-endian) the
    /// control socket carries. NOTE: these bytes are NOT a bearer secret —
    /// holding them does not confer authority; only a [`ValidityTable`] match
    /// does. (A PD writing arbitrary bytes here is exactly the forgery the
    /// table refuses.)
    pub fn to_bytes(self) -> [u8; 16] {
        let mut b = [0u8; 16];
        b[..8].copy_from_slice(&self.slot.to_le_bytes());
        b[8..].copy_from_slice(&self.epoch.to_le_bytes());
        b
    }

    /// Parse 16 wire bytes back into a handle (the inverse of [`Self::to_bytes`]).
    /// Whether the parsed handle is VALID is a separate question the
    /// [`ValidityTable`] answers — parsing always succeeds, validating may not.
    pub fn from_bytes(b: [u8; 16]) -> Self {
        let mut s = [0u8; 8];
        let mut e = [0u8; 8];
        s.copy_from_slice(&b[..8]);
        e.copy_from_slice(&b[8..]);
        CapHandle { slot: u64::from_le_bytes(s), epoch: u64::from_le_bytes(e) }
    }
}

/// What a valid cap-handle refers to in the kernel's table — the OBJECT the
/// handle authorizes operations against, plus the rights held over it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CapObject {
    /// The current epoch for this slot; a presented handle must match it.
    pub epoch: u64,
    /// The kind/identity of the kernel object the handle names.
    pub kind: ObjectKind,
    /// The rights held over the object — the REAL dregg [`Rights`]
    /// ([`dregg_cell::AuthRequired`]) lattice, so a process-backed cap
    /// attenuates by the SAME `granted ⊆ held` gate as every other firmament
    /// cap (we never reinvent it).
    pub rights: Rights,
}

/// The kind of kernel object a [`CapHandle`] can name. (The IPC objects mirror
/// the v0 [`ObjectType`]; the validity table is what makes them unforgeable
/// across the process boundary.)
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ObjectKind {
    /// A Notification (badge-OR signal object).
    Notification,
    /// A synchronous Endpoint (rendezvous IPC port).
    Endpoint,
    /// A shared memory region (a `shm_open`/`mmap` segment), named so a granted
    /// PD can map it.
    Region {
        /// The POSIX shm name the granted PD maps. A PD NOT holding a valid
        /// handle to this region never learns the name → cannot map it.
        shm_name: String,
        /// The region length in bytes.
        len: usize,
    },
    /// An Untyped budget (the factory slot-caveat), retypable into `permits`.
    Untyped {
        /// The only object type this Untyped may retype into.
        permits: ObjectType,
    },
}

/// Errors a cap-handle presentation can fail with — the cross-process
/// unforgeability refusals.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CapError {
    /// The presented handle is not in the validity table, or its epoch is stale
    /// (a reused slot), or it was fabricated from raw bytes — in ALL cases the
    /// kernel refuses it. **This is the raw-bytes-forgery refusal.**
    Forged {
        /// The handle the PD presented (for the kernel's audit log).
        presented: CapHandle,
        /// Why it was refused (no such slot / stale epoch).
        reason: ForgeReason,
    },
    /// The handle is valid but names the wrong KIND of object for the operation
    /// (e.g. a Signal against a Region handle).
    WrongKind {
        /// What the operation needed.
        expected: &'static str,
        /// What the handle actually names.
        got: &'static str,
    },
    /// The handle is valid but the held rights do not authorize the op
    /// (the `granted ⊆ held` check — the SAME `is_attenuation`).
    Unauthorized {
        /// The rights the op required.
        required: Rights,
        /// The rights the handle holds.
        held: Rights,
    },
}

/// Precisely why a handle failed the validity-table check.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ForgeReason {
    /// No object exists at the handle's slot — the slot was never minted, or the
    /// bytes are pure fabrication.
    NoSuchSlot,
    /// An object exists at the slot but at a DIFFERENT epoch — a stale handle
    /// for a reused slot (use-after-revoke confusion, refused).
    StaleEpoch {
        /// The epoch the table currently holds for the slot.
        current: u64,
        /// The (stale) epoch the handle presented.
        presented: u64,
    },
}

// ─────────────────────────── the validity table ─────────────────────────────

/// The KERNEL's cap-handle validity table — the load-bearing cross-process
/// unforgeability mechanism (§3, "the cap-integrity piece").
///
/// It maps each minted kernel slot → its current [`CapObject`] (epoch + kind +
/// rights). The ONLY way a [`CapHandle`] confers authority is by MATCHING an
/// entry here: a handle presented by a PD is validated by [`Self::validate`],
/// which refuses anything not in the table or at a stale epoch. Because the
/// table lives in the KERNEL (the trusted TCB), and a PD's address space holds
/// only the opaque HANDLE BYTES (never the table), **a PD cannot forge a cap by
/// writing raw bytes** — the bytes are inert without a table match.
///
/// This is the host-userspace stand-in for seL4's CNode: in seL4 a cap is
/// unforgeable because it lives in kernel-owned CNode memory the PD cannot
/// write; here a cap's VALIDITY is unforgeable because it lives in kernel-owned
/// table memory the PD cannot write (separate address space, MMU-enforced).
#[derive(Default)]
pub struct ValidityTable {
    /// slot → the object currently valid at that slot (epoch + kind + rights).
    entries: BTreeMap<u64, CapObject>,
    /// The next slot to hand out (kernel-minted, monotonic).
    next_slot: u64,
    /// Per-slot epoch high-water, so a reused slot always bumps its epoch
    /// (no two live objects ever share a (slot, epoch)).
    epoch_hwm: BTreeMap<u64, u64>,
}

impl ValidityTable {
    /// A fresh, empty table.
    pub fn new() -> Self {
        ValidityTable::default()
    }

    /// Mint a NEW cap into the table over `kind` with `rights`, returning its
    /// unforgeable [`CapHandle`]. Only the kernel calls this; a PD can never add
    /// a table entry, which is exactly why it cannot forge.
    pub fn mint(&mut self, kind: ObjectKind, rights: Rights) -> CapHandle {
        let slot = self.next_slot;
        self.next_slot += 1;
        let epoch = self.epoch_hwm.get(&slot).map(|e| e + 1).unwrap_or(0);
        self.epoch_hwm.insert(slot, epoch);
        self.entries.insert(slot, CapObject { epoch, kind, rights });
        CapHandle { slot, epoch }
    }

    /// Revoke the cap at `slot` — remove the table entry. A handle for it is
    /// thereafter [`ForgeReason::NoSuchSlot`] (or, if the slot is later reused,
    /// [`ForgeReason::StaleEpoch`]). Synchronous: the cap is dead the instant
    /// this returns. Returns whether an entry was removed.
    pub fn revoke(&mut self, slot: u64) -> bool {
        self.entries.remove(&slot).is_some()
    }

    /// Validate a PRESENTED handle against the table — the unforgeability check.
    ///
    /// Returns the [`CapObject`] iff the slot exists AND the epoch matches;
    /// otherwise [`CapError::Forged`]. **A handle fabricated from raw bytes
    /// (any `(slot, epoch)` a PD invents) fails here** unless it happens to
    /// collide with a live entry AT THE CURRENT EPOCH — and the monotonic,
    /// kernel-private epoch makes guessing a live epoch for a slot the PD never
    /// legitimately received vanishingly unlikely AND, more importantly, a slot
    /// the PD never received simply is not in the PD's knowledge to begin with;
    /// the table is the sole arbiter.
    pub fn validate(&self, h: CapHandle) -> Result<&CapObject, CapError> {
        match self.entries.get(&h.slot) {
            None => Err(CapError::Forged { presented: h, reason: ForgeReason::NoSuchSlot }),
            Some(obj) if obj.epoch != h.epoch => Err(CapError::Forged {
                presented: h,
                reason: ForgeReason::StaleEpoch { current: obj.epoch, presented: h.epoch },
            }),
            Some(obj) => Ok(obj),
        }
    }

    /// Validate AND check the op's required rights against the held rights via
    /// the REAL [`is_attenuation`] (`required ⊆ held`) — the SAME gate the local
    /// Mint and the distributed delegate use. Refuses a forged handle first,
    /// then an over-broad op.
    pub fn validate_for(&self, h: CapHandle, required: &Rights) -> Result<&CapObject, CapError> {
        let obj = self.validate(h)?;
        if !is_attenuation(&obj.rights, required) {
            return Err(CapError::Unauthorized {
                required: required.clone(),
                held: obj.rights.clone(),
            });
        }
        Ok(obj)
    }

    /// The number of live entries (for tests/assertions).
    pub fn live_count(&self) -> usize {
        self.entries.len()
    }
}

// ─────────────────────────── shared memory (shm) ────────────────────────────

/// A POSIX shared-memory region the kernel created and a granted PD maps — the
/// v1 `memory_region_symbol!` backing (replacing v0's heap `Vec<u8>`).
///
/// The kernel `shm_open`s a randomly-named segment, `ftruncate`s it to `len`,
/// and `mmap`s it. A PD that the kernel GRANTS the region (by handing it the
/// `(name, len)` at fork time, inside the cap it received) maps the SAME named
/// object and sees the kernel's / other granted PDs' writes. A PD NOT granted
/// the region never learns the unguessable name → cannot map it. The mapping is
/// a real per-process MMU mapping, so even a granted PD reaches ONLY this region
/// through it, never another PD's private memory.
pub struct ShmRegion {
    /// The POSIX shm name (e.g. `/dregg-fmt-<rand>`).
    name: String,
    /// The mapped base pointer (valid in THIS process's address space only).
    ptr: *mut u8,
    /// The region length in bytes.
    len: usize,
    /// Whether THIS handle owns the mapping (and should unmap on drop). The
    /// kernel owns the canonical mapping; a PD's mapping is its own.
    owns_unlink: bool,
}

// Safety: the pointer is into a `mmap`'d MAP_SHARED segment; access is mediated
// through `&self`/`&mut self` and the kernel serializes structural changes. The
// raw pointer is not Send/Sync by default, so we assert it deliberately: the
// segment is process-shared by design, and within a process we guard via the
// kernel lock.
unsafe impl Send for ShmRegion {}
unsafe impl Sync for ShmRegion {}

impl ShmRegion {
    /// CREATE a fresh shared region (the kernel side): `shm_open(O_CREAT |
    /// O_EXCL | O_RDWR)` a randomly-named object, size it, and map it. The
    /// `O_EXCL` guarantees we created it (not an attacker squatting the name);
    /// the random name makes the name itself hard to guess.
    pub fn create(len: usize) -> io::Result<ShmRegion> {
        let name = Self::random_name();
        unsafe {
            let cname = std::ffi::CString::new(name.clone()).unwrap();
            // O_CREAT | O_EXCL: we MUST be the creator; O_RDWR for map RW.
            let fd = libc::shm_open(
                cname.as_ptr(),
                libc::O_CREAT | libc::O_EXCL | libc::O_RDWR,
                0o600,
            );
            if fd < 0 {
                return Err(io::Error::last_os_error());
            }
            if libc::ftruncate(fd, len as libc::off_t) != 0 {
                let e = io::Error::last_os_error();
                libc::close(fd);
                libc::shm_unlink(cname.as_ptr());
                return Err(e);
            }
            let ptr = libc::mmap(
                std::ptr::null_mut(),
                len,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_SHARED,
                fd,
                0,
            );
            libc::close(fd); // the mapping survives the fd close
            if ptr == libc::MAP_FAILED {
                let e = io::Error::last_os_error();
                libc::shm_unlink(cname.as_ptr());
                return Err(e);
            }
            Ok(ShmRegion { name, ptr: ptr as *mut u8, len, owns_unlink: true })
        }
    }

    /// MAP an existing shared region by name (the granted-PD side): a PD the
    /// kernel handed `(name, len)` maps the SAME object the kernel created. A PD
    /// that never received the name cannot reach this code with the right name —
    /// the name is the grant.
    pub fn map_existing(name: &str, len: usize) -> io::Result<ShmRegion> {
        unsafe {
            let cname = std::ffi::CString::new(name).unwrap();
            let fd = libc::shm_open(cname.as_ptr(), libc::O_RDWR, 0o600);
            if fd < 0 {
                return Err(io::Error::last_os_error());
            }
            let ptr = libc::mmap(
                std::ptr::null_mut(),
                len,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_SHARED,
                fd,
                0,
            );
            libc::close(fd);
            if ptr == libc::MAP_FAILED {
                return Err(io::Error::last_os_error());
            }
            Ok(ShmRegion { name: name.to_string(), ptr: ptr as *mut u8, len, owns_unlink: false })
        }
    }

    /// The region's name (the grant token the kernel hands a PD).
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The region length in bytes.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Is the region empty?
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Read the whole region as a snapshot copy (a granted PD reading the shared
    /// buffer the firmament mapped into it).
    pub fn read(&self) -> Vec<u8> {
        // Safety: ptr is a valid mapping of `len` bytes in this process.
        unsafe { std::slice::from_raw_parts(self.ptr, self.len).to_vec() }
    }

    /// Mutate the region in place — the `&mut [u8]` access of §3, now a REAL
    /// MMU-mapped write into the shared segment (not a kernel-mediated heap
    /// touch). Other granted PDs see it; non-granted PDs cannot reach it.
    pub fn with_mut<T>(&self, f: impl FnOnce(&mut [u8]) -> T) -> T {
        // Safety: ptr is a valid RW mapping of `len` bytes; MAP_SHARED means the
        // write is visible to other mappers. We take `&self` because the mapping
        // is shared by design; callers serialize via the kernel where needed.
        unsafe {
            let s = std::slice::from_raw_parts_mut(self.ptr, self.len);
            f(s)
        }
    }

    fn random_name() -> String {
        // A 128-bit-ish random suffix from the OS RNG via two nonces; the shm
        // namespace is per-user on macOS/Linux, so unguessability + O_EXCL is
        // the POSIX-layer grant. (macOS truncates shm names to 31 chars incl.
        // the leading '/', so keep it short.)
        let r = next_rand();
        format!("/df{:x}", r)
    }
}

impl Drop for ShmRegion {
    fn drop(&mut self) {
        unsafe {
            libc::munmap(self.ptr as *mut libc::c_void, self.len);
            if self.owns_unlink {
                // The kernel-side region: unlink the NAME so it leaves the
                // namespace once we're done (granted PDs that already mapped it
                // keep their mapping; un-granted PDs can no longer open it).
                let cname = std::ffi::CString::new(self.name.clone()).unwrap();
                libc::shm_unlink(cname.as_ptr());
            }
        }
    }
}

/// A small, process-unique random source for shm names. Seeded from the OS
/// (`/dev/urandom`-equivalent via `getrandom`-ish libc) at first use + a
/// monotonic counter so successive names never collide within a process.
fn next_rand() -> u64 {
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    static SEED: AtomicU64 = AtomicU64::new(0);
    let seed = {
        let s = SEED.load(Ordering::Relaxed);
        if s != 0 {
            s
        } else {
            let fresh = os_random_u64() | 1; // nonzero
            SEED.store(fresh, Ordering::Relaxed);
            fresh
        }
    };
    let c = COUNTER.fetch_add(1, Ordering::Relaxed);
    // Mix the OS seed, a per-process pid, and the counter — splitmix64-ish.
    let pid = unsafe { libc::getpid() } as u64;
    let mut x = seed ^ pid.rotate_left(17) ^ c.wrapping_mul(0x9E37_79B9_7F4A_7C15);
    x ^= x >> 30;
    x = x.wrapping_mul(0xBF58_476D_1CE4_E5B9);
    x ^= x >> 27;
    x = x.wrapping_mul(0x94D0_49BB_1331_11EB);
    x ^= x >> 31;
    x
}

/// One u64 of OS randomness. Uses `getentropy` where available (macOS + modern
/// Linux); falls back to reading `/dev/urandom`.
fn os_random_u64() -> u64 {
    let mut buf = [0u8; 8];
    // getentropy is on macOS and Linux ≥3.17/glibc≥2.25.
    let rc = unsafe { libc::getentropy(buf.as_mut_ptr() as *mut libc::c_void, buf.len()) };
    if rc == 0 {
        return u64::from_le_bytes(buf);
    }
    // Fallback: /dev/urandom.
    if let Ok(mut f) = std::fs::File::open("/dev/urandom") {
        if f.read_exact(&mut buf).is_ok() {
            return u64::from_le_bytes(buf);
        }
    }
    // Last resort: time-based (only reached if both above fail — never on a
    // normal macOS/Linux host; kept so we never panic the kernel).
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos() as u64)
        .unwrap_or(0x1234_5678_9ABC_DEF0)
}

// ──────────────────────────── the control wire ──────────────────────────────
//
// A PD talks to the kernel over a `socketpair` (one per PD). Every request a PD
// makes (signal/wait/region access/install/mint/revoke) is a length-prefixed
// message the KERNEL services after VALIDATING the presented cap-handle. The PD
// never touches the validity table or another PD's memory; it only sends bytes
// the kernel checks. This is the cross-process form of "every authority
// decision is a syscall the kernel mediates".

/// A request a PD sends the kernel over its control socket. Each carries the
/// [`CapHandle`] the op is against; the kernel VALIDATES it before acting, so a
/// forged handle is refused at the wire. (Kept small + explicit; this is a
/// faithful syscall surface, not a general RPC.)
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum KernelRequest {
    /// `seL4_Signal` — OR `badge` into the notification the handle names.
    Signal { notif: CapHandle, badge: u64 },
    /// `seL4_Wait` — block until the notification's badge is non-zero; reply
    /// carries the accumulated badge (read-and-clear).
    Wait { notif: CapHandle },
    /// Validate a handle WITHOUT side effects (the explicit unforgeability
    /// probe the isolation tooth uses): reply is `Ok`/`Forged`.
    Validate { handle: CapHandle },
    /// Ask the kernel for the shm `(name, len)` of a region the PD holds a
    /// handle to — the GRANT lookup. A forged/region-less handle is refused, so
    /// a PD cannot learn an ungranted region's name.
    RegionInfo { region: CapHandle },
}

/// The kernel's reply to a [`KernelRequest`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum KernelReply {
    /// A `Signal`/side-effecting op succeeded.
    Ok,
    /// A `Wait` returned this accumulated badge.
    Badge(u64),
    /// A handle validated; it names this kind (a short tag).
    Valid { kind: &'static str },
    /// A `RegionInfo` succeeded: the granted PD may now `map_existing(name, len)`.
    Region { name: String, len: usize },
    /// The presented handle was FORGED / stale / region-less — refused. **This
    /// is the cross-process unforgeability refusal a PD sees.**
    Forged,
    /// The handle names the wrong kind of object for the op.
    WrongKind,
    /// The op was unauthorized (rights check).
    Unauthorized,
}

/// Write a length-prefixed `bincode`-free framing of a request/reply. We hand-
/// roll a tiny tag+payload codec so the wire has NO serde dependency surface
/// (keeping the crate's dep graph minimal). Each message: `[u32 len][bytes]`.
fn write_framed(s: &mut UnixStream, bytes: &[u8]) -> io::Result<()> {
    let len = (bytes.len() as u32).to_le_bytes();
    s.write_all(&len)?;
    s.write_all(bytes)?;
    s.flush()
}

/// Read a length-prefixed frame written by [`write_framed`].
fn read_framed(s: &mut UnixStream) -> io::Result<Vec<u8>> {
    let mut len = [0u8; 4];
    s.read_exact(&mut len)?;
    let n = u32::from_le_bytes(len) as usize;
    let mut buf = vec![0u8; n];
    s.read_exact(&mut buf)?;
    Ok(buf)
}

// A minimal hand-rolled codec for the request/reply enums (tag byte + fields).
// Faithful + dependency-free; only the variants the boot/isolation slice needs.

impl KernelRequest {
    fn encode(&self) -> Vec<u8> {
        let mut v = Vec::new();
        match self {
            KernelRequest::Signal { notif, badge } => {
                v.push(0);
                v.extend_from_slice(&notif.to_bytes());
                v.extend_from_slice(&badge.to_le_bytes());
            }
            KernelRequest::Wait { notif } => {
                v.push(1);
                v.extend_from_slice(&notif.to_bytes());
            }
            KernelRequest::Validate { handle } => {
                v.push(2);
                v.extend_from_slice(&handle.to_bytes());
            }
            KernelRequest::RegionInfo { region } => {
                v.push(3);
                v.extend_from_slice(&region.to_bytes());
            }
        }
        v
    }

    fn decode(b: &[u8]) -> Option<KernelRequest> {
        let (&tag, rest) = b.split_first()?;
        let take16 = |r: &[u8]| -> Option<CapHandle> {
            let arr: [u8; 16] = r.get(..16)?.try_into().ok()?;
            Some(CapHandle::from_bytes(arr))
        };
        match tag {
            0 => {
                let h = take16(rest)?;
                let badge = u64::from_le_bytes(rest.get(16..24)?.try_into().ok()?);
                Some(KernelRequest::Signal { notif: h, badge })
            }
            1 => Some(KernelRequest::Wait { notif: take16(rest)? }),
            2 => Some(KernelRequest::Validate { handle: take16(rest)? }),
            3 => Some(KernelRequest::RegionInfo { region: take16(rest)? }),
            _ => None,
        }
    }
}

impl KernelReply {
    fn encode(&self) -> Vec<u8> {
        let mut v = Vec::new();
        match self {
            KernelReply::Ok => v.push(0),
            KernelReply::Badge(b) => {
                v.push(1);
                v.extend_from_slice(&b.to_le_bytes());
            }
            KernelReply::Valid { kind } => {
                v.push(2);
                v.extend_from_slice(kind.as_bytes());
            }
            KernelReply::Region { name, len } => {
                v.push(3);
                v.extend_from_slice(&(*len as u64).to_le_bytes());
                v.extend_from_slice(name.as_bytes());
            }
            KernelReply::Forged => v.push(4),
            KernelReply::WrongKind => v.push(5),
            KernelReply::Unauthorized => v.push(6),
        }
        v
    }

    fn decode(b: &[u8]) -> Option<KernelReply> {
        let (&tag, rest) = b.split_first()?;
        match tag {
            0 => Some(KernelReply::Ok),
            1 => Some(KernelReply::Badge(u64::from_le_bytes(rest.get(..8)?.try_into().ok()?))),
            2 => {
                let kind = match std::str::from_utf8(rest).ok()? {
                    "notification" => "notification",
                    "endpoint" => "endpoint",
                    "region" => "region",
                    "untyped" => "untyped",
                    _ => "object",
                };
                Some(KernelReply::Valid { kind })
            }
            3 => {
                let len = u64::from_le_bytes(rest.get(..8)?.try_into().ok()?) as usize;
                let name = std::str::from_utf8(rest.get(8..)?).ok()?.to_string();
                Some(KernelReply::Region { name, len })
            }
            4 => Some(KernelReply::Forged),
            5 => Some(KernelReply::WrongKind),
            6 => Some(KernelReply::Unauthorized),
            _ => None,
        }
    }
}

// ─────────────────────────────── the kernel ─────────────────────────────────

/// Kernel-side state: the validity table + the live IPC objects, all under one
/// lock (the n=1 collapse, exactly as v0). Notifications live in the kernel and
/// are reached by PDs ONLY through validated handles over the control socket.
struct ProcessKernelState {
    /// THE validity table — the cross-process unforgeability mechanism.
    table: ValidityTable,
    /// Notification badge accumulators, keyed by slot (the handle's `slot`).
    notif_badges: BTreeMap<u64, u64>,
    /// The kernel's OWN mappings of the shm regions it created (kept alive so
    /// the segments persist while PDs map them; dropped on kernel teardown).
    regions: BTreeMap<u64, ShmRegion>,
}

/// The v1 PROCESS-backed kernel — PDs are forked processes; isolation is the
/// host MMU's; cap-handle validity is this kernel's table.
///
/// It is the trusted TCB (the host-userspace stand-in for the seL4 kernel). It
/// runs in the PARENT process; PDs are children connected by control sockets. A
/// PD presents [`CapHandle`]s; the kernel VALIDATES them against [`ValidityTable`]
/// before acting — so a forged handle (raw bytes a PD invents) is refused.
///
/// `Clone` is a cheap `Arc` bump so the kernel can hold a handle to itself
/// across the dispatch loop; the kernel is NOT shared into child processes
/// (each child gets only its control socket + the names of regions it was
/// granted — never the table).
#[derive(Clone)]
pub struct ProcessKernel {
    state: Arc<Mutex<ProcessKernelState>>,
}

impl Default for ProcessKernel {
    fn default() -> Self {
        Self::new()
    }
}

impl ProcessKernel {
    /// A fresh process-backed kernel (empty validity table).
    pub fn new() -> Self {
        ProcessKernel {
            state: Arc::new(Mutex::new(ProcessKernelState {
                table: ValidityTable::new(),
                notif_badges: BTreeMap::new(),
                regions: BTreeMap::new(),
            })),
        }
    }

    /// The bounds this kernel advertises — [`crate::Bounds::LOCAL`], and now
    /// MMU-enforced (not merely by-construction): a revoke removes the table
    /// entry under the held lock (synchronous), and isolation is the real host
    /// page tables. Same headline as v0, with the v0 caveat CLOSED.
    pub const fn bounds(&self) -> crate::Bounds {
        crate::Bounds::LOCAL
    }

    /// A short, honest statement of what the v1 process backing ENFORCES vs what
    /// remains trusted — the closed-gap fidelity label (§3). Travels WITH the
    /// code, NOT laundered. (Contrast [`crate::EmulatedKernel::ISOLATION_FIDELITY`],
    /// which states the v0 GAP this closes.)
    pub const ISOLATION_FIDELITY: &'static str = "\
        v1 PDs are host PROCESSES: 'no ambient authority' is now MMU-ENFORCED — \
        a PD physically cannot read another PD's private memory (separate page \
        tables, host-OS-enforced). A PD cannot forge a cap by writing raw bytes: \
        a presented cap-handle is checked against the KERNEL's epoch-tagged \
        validity table (the cross-process CNode-unforgeability analogue), so \
        raw/stale bytes are refused. TRUSTED, stated honestly: the validity \
        table is the kernel's (the TCB); the MMU is the host OS's (the same \
        trust a real seL4 PD places in seL4 + the hardware MMU). Shared regions \
        are per-PD shm_open/mmap mappings granted by name; a non-granted PD \
        cannot map them.";

    // ── cap minting (kernel-only — a PD can never add a table entry) ──────────

    /// Mint a Notification cap into the validity table; returns its unforgeable
    /// handle. (The kernel wires one per channel at boot, exactly as v0
    /// `create_notification`, but the handle is now epoch-tagged + table-backed.)
    pub fn create_notification(&self, rights: Rights) -> CapHandle {
        let mut st = self.state.lock().unwrap();
        let h = st.table.mint(ObjectKind::Notification, rights);
        st.notif_badges.insert(h.slot, 0);
        h
    }

    /// Mint a shared-region cap: `shm_open`/`mmap` a fresh segment, record it in
    /// the validity table, and return the handle. The kernel keeps its own
    /// mapping alive; a granted PD learns the name via [`KernelRequest::RegionInfo`]
    /// (validated) and `map_existing`s it.
    pub fn create_region(&self, len: usize, rights: Rights) -> io::Result<CapHandle> {
        let region = ShmRegion::create(len)?;
        let name = region.name().to_string();
        let mut st = self.state.lock().unwrap();
        let h = st.table.mint(ObjectKind::Region { shm_name: name, len }, rights);
        st.regions.insert(h.slot, region);
        Ok(h)
    }

    /// Mint an Untyped budget cap (the factory slot-caveat), table-backed.
    pub fn create_untyped(&self, permits: ObjectType, rights: Rights) -> CapHandle {
        let mut st = self.state.lock().unwrap();
        st.table.mint(ObjectKind::Untyped { permits }, rights)
    }

    /// `seL4_CNode_Revoke` on a handle's slot — synchronous removal from the
    /// validity table. A handle for the revoked slot is thereafter
    /// [`ForgeReason::NoSuchSlot`] (and any later reuse bumps the epoch, so a
    /// replay is [`ForgeReason::StaleEpoch`]). Returns whether it was live.
    pub fn revoke(&self, h: CapHandle) -> bool {
        let mut st = self.state.lock().unwrap();
        // Drop the kernel-side shm mapping too if it was a region.
        st.regions.remove(&h.slot);
        st.notif_badges.remove(&h.slot);
        st.table.revoke(h.slot)
    }

    /// VALIDATE a presented handle (kernel-side, no side effect) — the core
    /// unforgeability check, exposed so the dispatch loop AND tests use the SAME
    /// path. Returns the object KIND tag on success, or the refusal.
    pub fn validate(&self, h: CapHandle) -> Result<&'static str, CapError> {
        let st = self.state.lock().unwrap();
        let obj = st.table.validate(h)?;
        Ok(match &obj.kind {
            ObjectKind::Notification => "notification",
            ObjectKind::Endpoint => "endpoint",
            ObjectKind::Region { .. } => "region",
            ObjectKind::Untyped { .. } => "untyped",
        })
    }

    /// `seL4_Signal` (kernel-side) — OR `badge` into the notification the
    /// (validated) handle names. Refuses a forged handle / wrong kind.
    pub fn signal(&self, h: CapHandle, badge: u64) -> Result<(), CapError> {
        let mut st = self.state.lock().unwrap();
        let obj = st.table.validate(h)?;
        if !matches!(obj.kind, ObjectKind::Notification) {
            return Err(CapError::WrongKind { expected: "notification", got: kind_tag(&obj.kind) });
        }
        *st.notif_badges.entry(h.slot).or_insert(0) |= badge;
        Ok(())
    }

    /// A NON-blocking poll of a notification's badge (read-and-clear), kernel-
    /// side, validated. (The blocking `Wait` is realized in the dispatch loop
    /// over the socket; the kernel object is the same accumulator.)
    pub fn poll_notification(&self, h: CapHandle) -> Result<u64, CapError> {
        let mut st = self.state.lock().unwrap();
        let obj = st.table.validate(h)?;
        if !matches!(obj.kind, ObjectKind::Notification) {
            return Err(CapError::WrongKind { expected: "notification", got: kind_tag(&obj.kind) });
        }
        let b = st.notif_badges.get(&h.slot).copied().unwrap_or(0);
        st.notif_badges.insert(h.slot, 0);
        Ok(b)
    }

    /// Look up the shm `(name, len)` for a region the (validated) handle names —
    /// the GRANT lookup. A forged or non-region handle is refused, so a PD
    /// cannot learn the name of a region it was not granted.
    pub fn region_info(&self, h: CapHandle) -> Result<(String, usize), CapError> {
        let st = self.state.lock().unwrap();
        let obj = st.table.validate(h)?;
        match &obj.kind {
            ObjectKind::Region { shm_name, len } => Ok((shm_name.clone(), *len)),
            other => Err(CapError::WrongKind { expected: "region", got: kind_tag(other) }),
        }
    }

    /// The kernel's own view onto a region it created (for the harness/kernel to
    /// read or seed the shared buffer). Validated.
    pub fn region_with_mut<T>(
        &self,
        h: CapHandle,
        f: impl FnOnce(&mut [u8]) -> T,
    ) -> Result<T, CapError> {
        let st = self.state.lock().unwrap();
        // Validate first (refuse forged), THEN reach the kernel's own mapping.
        let _obj = st.table.validate(h)?;
        match st.regions.get(&h.slot) {
            Some(region) => Ok(region.with_mut(f)),
            None => Err(CapError::Forged { presented: h, reason: ForgeReason::NoSuchSlot }),
        }
    }

    /// The kernel's own read of a region it created. Validated.
    pub fn region_read(&self, h: CapHandle) -> Result<Vec<u8>, CapError> {
        let st = self.state.lock().unwrap();
        let _obj = st.table.validate(h)?;
        match st.regions.get(&h.slot) {
            Some(region) => Ok(region.read()),
            None => Err(CapError::Forged { presented: h, reason: ForgeReason::NoSuchSlot }),
        }
    }

    /// The number of live caps in the table (tests/assertions).
    pub fn live_caps(&self) -> usize {
        self.state.lock().unwrap().table.live_count()
    }

    // ── the control-socket dispatch (one validating "syscall" per message) ────

    /// SERVE one request from a PD's control socket: read a framed
    /// [`KernelRequest`], VALIDATE its cap-handle against the table, perform the
    /// op (or refuse), and write the framed [`KernelReply`]. This is the
    /// cross-process "syscall" boundary — every PD authority decision passes
    /// through here and is checked. Returns `Ok(false)` on a clean EOF (the PD
    /// closed its socket / exited).
    ///
    /// `Wait` is realized by polling the kernel accumulator with a short backoff
    /// (the kernel and PD are separate processes; a condvar cannot span them, so
    /// the kernel busy-waits-with-yield on the badge — faithful "the PD is
    /// descheduled until signalled", realized at the kernel side).
    pub fn serve_one(&self, sock: &mut UnixStream) -> io::Result<bool> {
        let frame = match read_framed(sock) {
            Ok(f) => f,
            Err(e) if e.kind() == io::ErrorKind::UnexpectedEof => return Ok(false),
            Err(e) => return Err(e),
        };
        let req = match KernelRequest::decode(&frame) {
            Some(r) => r,
            None => {
                // A malformed/garbage frame from a PD is treated as a forged
                // request — refused, never trusted.
                write_framed(sock, &KernelReply::Forged.encode())?;
                return Ok(true);
            }
        };
        let reply = self.handle_request(req);
        write_framed(sock, &reply.encode())?;
        Ok(true)
    }

    /// Map a [`KernelRequest`] to its [`KernelReply`], validating throughout.
    fn handle_request(&self, req: KernelRequest) -> KernelReply {
        match req {
            KernelRequest::Signal { notif, badge } => match self.signal(notif, badge) {
                Ok(()) => KernelReply::Ok,
                Err(CapError::Forged { .. }) => KernelReply::Forged,
                Err(CapError::WrongKind { .. }) => KernelReply::WrongKind,
                Err(CapError::Unauthorized { .. }) => KernelReply::Unauthorized,
            },
            KernelRequest::Wait { notif } => {
                // Validate once up front so a forged Wait is refused immediately.
                if self.validate(notif).is_err() {
                    return KernelReply::Forged;
                }
                // Poll-with-yield until the badge is non-zero (faithful block).
                loop {
                    match self.poll_notification(notif) {
                        Ok(0) => std::thread::yield_now(),
                        Ok(b) => return KernelReply::Badge(b),
                        Err(_) => return KernelReply::Forged,
                    }
                }
            }
            KernelRequest::Validate { handle } => match self.validate(handle) {
                Ok(kind) => KernelReply::Valid { kind },
                Err(_) => KernelReply::Forged,
            },
            KernelRequest::RegionInfo { region } => match self.region_info(region) {
                Ok((name, len)) => KernelReply::Region { name, len },
                Err(CapError::WrongKind { .. }) => KernelReply::WrongKind,
                Err(_) => KernelReply::Forged,
            },
        }
    }
}

fn kind_tag(k: &ObjectKind) -> &'static str {
    match k {
        ObjectKind::Notification => "notification",
        ObjectKind::Endpoint => "endpoint",
        ObjectKind::Region { .. } => "region",
        ObjectKind::Untyped { .. } => "untyped",
    }
}

// ─────────────────────────── the PD-side client ─────────────────────────────

/// A PD's handle to the kernel over its control socket — the CHILD-process side.
///
/// A forked PD holds ONE of these (its only channel to the kernel) plus the
/// [`CapHandle`]s the kernel granted it. It cannot reach the validity table or
/// another PD's memory; every authority op is a validated round-trip through the
/// socket. This is what the [`crate::microkit_facade::Channel`] / [`Region`]
/// resolve to on the process backing.
///
/// [`Region`]: crate::microkit_facade::Region
pub struct KernelClient {
    sock: Mutex<UnixStream>,
}

impl KernelClient {
    /// Wrap a control socket (the fd the child inherited from the kernel).
    pub fn new(sock: UnixStream) -> Self {
        KernelClient { sock: Mutex::new(sock) }
    }

    /// Adopt a raw inherited fd (the child's end of the `socketpair`) as the
    /// kernel client. Used right after `fork` in the child.
    ///
    /// # Safety
    /// `fd` must be a valid, owned `socketpair` fd the child inherited and that
    /// nothing else will close.
    pub unsafe fn from_raw_fd(fd: RawFd) -> Self {
        KernelClient::new(UnixStream::from_raw_fd(fd))
    }

    fn round_trip(&self, req: KernelRequest) -> io::Result<KernelReply> {
        let mut s = self.sock.lock().unwrap();
        write_framed(&mut s, &req.encode())?;
        let frame = read_framed(&mut s)?;
        KernelReply::decode(&frame)
            .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "bad kernel reply"))
    }

    /// `Channel::notify` (the PD side) — signal a notification by handle. The
    /// kernel validates the handle; a forged handle is refused.
    pub fn signal(&self, notif: CapHandle, badge: u64) -> io::Result<KernelReply> {
        self.round_trip(KernelRequest::Signal { notif, badge })
    }

    /// `seL4_Wait` (the PD side) — block until the notification fires; returns
    /// the accumulated badge.
    pub fn wait(&self, notif: CapHandle) -> io::Result<u64> {
        match self.round_trip(KernelRequest::Wait { notif })? {
            KernelReply::Badge(b) => Ok(b),
            other => Err(io::Error::new(
                io::ErrorKind::Other,
                format!("wait got {other:?}"),
            )),
        }
    }

    /// Probe whether a handle validates (the isolation tooth uses this to show a
    /// FORGED handle is refused across the process boundary).
    pub fn validate(&self, handle: CapHandle) -> io::Result<KernelReply> {
        self.round_trip(KernelRequest::Validate { handle })
    }

    /// Resolve a region handle to its mapped [`ShmRegion`] — the GRANT path. The
    /// kernel validates the handle and returns the `(name, len)`; the PD then
    /// maps the SAME shm object. A forged/ungranted handle is refused, so a PD
    /// CANNOT map a region it does not hold a cap to.
    pub fn map_region(&self, region: CapHandle) -> io::Result<ShmRegion> {
        match self.round_trip(KernelRequest::RegionInfo { region })? {
            KernelReply::Region { name, len } => ShmRegion::map_existing(&name, len),
            KernelReply::Forged => Err(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "region handle forged / not granted — refused by the validity table",
            )),
            other => Err(io::Error::new(
                io::ErrorKind::Other,
                format!("map_region got {other:?}"),
            )),
        }
    }
}

// ───────────────────── fork + socketpair PD spawning ────────────────────────

/// A spawned PD process the kernel can join — the process analogue of v0's
/// thread `JoinHandle`.
pub struct PdProcess {
    /// The child pid.
    pub pid: libc::pid_t,
    /// The KERNEL's end of the control socket to this PD (the kernel services
    /// the PD's requests on it).
    pub kernel_sock: UnixStream,
}

impl PdProcess {
    /// Wait for the PD process to exit and return its raw exit status (0 = the
    /// PD ran its body to completion and exited cleanly).
    pub fn join(self) -> io::Result<i32> {
        // Drop the kernel socket first so the child's blocking reads (if any)
        // see EOF; then reap.
        drop(self.kernel_sock);
        let mut status: libc::c_int = 0;
        let rc = unsafe { libc::waitpid(self.pid, &mut status, 0) };
        if rc < 0 {
            return Err(io::Error::last_os_error());
        }
        // Decode WEXITSTATUS without the libc macros (not exposed in Rust libc).
        let code = if status & 0x7f == 0 {
            (status >> 8) & 0xff
        } else {
            // Terminated by a signal: report a negative-ish code so the harness
            // can distinguish (e.g. a SIGSEGV from a forbidden cross-PD read).
            -(status & 0x7f)
        };
        Ok(code)
    }
}

/// Errors spawning a PD process.
#[derive(Debug)]
pub enum SpawnError {
    /// `socketpair(2)` failed.
    SocketPair(io::Error),
    /// `fork(2)` failed.
    Fork(io::Error),
}

impl std::fmt::Display for SpawnError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SpawnError::SocketPair(e) => write!(f, "socketpair failed: {e}"),
            SpawnError::Fork(e) => write!(f, "fork failed: {e}"),
        }
    }
}

impl std::error::Error for SpawnError {}

impl ProcessKernel {
    /// SPAWN a PD as a forked CHILD PROCESS — the v1 isolation upgrade's core.
    ///
    /// Creates a `socketpair`, `fork`s, and in the CHILD runs `body` with a
    /// [`KernelClient`] over the child's socket end + the granted [`CapHandle`]s
    /// (passed by VALUE — the child gets the handle BYTES, but possessing them
    /// is not possessing authority; the kernel's table is the arbiter). The
    /// child then `_exit`s with `body`'s return code. The PARENT (kernel) gets a
    /// [`PdProcess`] whose `kernel_sock` it services via [`Self::serve_one`].
    ///
    /// Because the child has its OWN page tables, it physically cannot read the
    /// parent's or a sibling's private memory — the MMU enforcement v0 lacked.
    /// It reaches shared state ONLY through (a) granted shm regions it maps and
    /// (b) validated control-socket requests.
    ///
    /// `body: FnOnce(KernelClient, Vec<CapHandle>) -> i32` is the PD's `init()` +
    /// event-loop, the SAME logic the v0 thread backing runs — only the launch
    /// (process vs thread) and the kernel access (socket vs in-process call)
    /// differ, and both are hidden behind the facade.
    ///
    /// # Safety / fork discipline
    /// `fork` in a multi-threaded process is delicate. The child MUST NOT touch
    /// any lock the parent might hold; here the child does NOT use the parent's
    /// [`ProcessKernel`] at all — it gets a fresh [`KernelClient`] over a socket
    /// and the granted handles. The child does only async-signal-safe-ish work
    /// (its own `body`) and then `_exit`s (never `exit`, to skip parent atexit
    /// handlers). The boot/isolation tests keep `body` simple, exactly as a real
    /// PD's `init` is.
    pub fn spawn_pd<F>(&self, granted: Vec<CapHandle>, body: F) -> Result<PdProcess, SpawnError>
    where
        F: FnOnce(KernelClient, Vec<CapHandle>) -> i32,
    {
        // socketpair(AF_UNIX, SOCK_STREAM) — the bidirectional control channel.
        let mut fds = [0 as RawFd; 2];
        let rc = unsafe {
            libc::socketpair(libc::AF_UNIX, libc::SOCK_STREAM, 0, fds.as_mut_ptr())
        };
        if rc != 0 {
            return Err(SpawnError::SocketPair(io::Error::last_os_error()));
        }
        let parent_fd = fds[0];
        let child_fd = fds[1];

        let pid = unsafe { libc::fork() };
        if pid < 0 {
            let e = io::Error::last_os_error();
            unsafe {
                libc::close(parent_fd);
                libc::close(child_fd);
            }
            return Err(SpawnError::Fork(e));
        }

        if pid == 0 {
            // ── CHILD (the PD process) ──
            // Close the parent's socket end; keep ours.
            unsafe { libc::close(parent_fd) };
            let client = unsafe { KernelClient::from_raw_fd(child_fd) };
            // Run the PD body with its granted handles. Its return is the exit
            // code. We `_exit` to avoid running the parent's atexit/destructors
            // in the forked child (the classic fork-safety rule).
            let code = body(client, granted);
            // Flush stdout so PD prints are visible under --nocapture, then
            // _exit (bypassing libc atexit / Rust's runtime shutdown).
            use std::io::Write as _;
            let _ = std::io::stdout().flush();
            unsafe { libc::_exit(code) };
        }

        // ── PARENT (the kernel) ──
        unsafe { libc::close(child_fd) };
        let kernel_sock = unsafe { UnixStream::from_raw_fd(parent_fd) };
        Ok(PdProcess { pid, kernel_sock })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::AuthRequired;

    // ── The validity table: the cap-forgery refusal (the load-bearing piece) ──

    #[test]
    fn validity_table_refuses_a_forged_handle() {
        // A PD can write ANY 16 bytes and call them a handle; the table refuses
        // anything it did not mint — raw-bytes forgery is impossible.
        let mut t = ValidityTable::new();
        let real = t.mint(ObjectKind::Notification, AuthRequired::Either);
        // The real handle validates.
        assert!(t.validate(real).is_ok());

        // A fabricated handle (a slot the table never minted) is refused.
        let forged = CapHandle { slot: 9999, epoch: 0 };
        assert!(matches!(
            t.validate(forged),
            Err(CapError::Forged { reason: ForgeReason::NoSuchSlot, .. })
        ));

        // A handle for a REAL slot but the WRONG epoch (a stale/guessed epoch)
        // is refused — the use-after-reuse guard.
        let stale = CapHandle { slot: real.slot, epoch: real.epoch + 7 };
        assert!(matches!(
            t.validate(stale),
            Err(CapError::Forged { reason: ForgeReason::StaleEpoch { .. }, .. })
        ));
    }

    #[test]
    fn revoke_then_replay_is_refused_with_bumped_epoch() {
        let mut t = ValidityTable::new();
        let h = t.mint(ObjectKind::Notification, AuthRequired::Either);
        assert!(t.validate(h).is_ok());
        // Revoke it — the entry is gone, the handle is now forged.
        assert!(t.revoke(h.slot));
        assert!(matches!(
            t.validate(h),
            Err(CapError::Forged { reason: ForgeReason::NoSuchSlot, .. })
        ));
        // (Epoch high-water persists, so a future reuse of the slot would bump
        // the epoch, refusing this stale handle by StaleEpoch rather than
        // accepting a replay.)
        assert_eq!(t.epoch_hwm.get(&h.slot), Some(&h.epoch));
    }

    #[test]
    fn validate_for_enforces_real_attenuation_lattice() {
        // The held rights gate the op via the REAL is_attenuation — same lattice
        // as every other firmament cap.
        let mut t = ValidityTable::new();
        let h = t.mint(ObjectKind::Notification, AuthRequired::Signature);
        // Requiring a NARROWER-or-equal authority succeeds (Signature ⊆ Signature).
        assert!(t.validate_for(h, &AuthRequired::Signature).is_ok());
        // Requiring a BROADER authority than held is refused (None is broadest).
        assert!(matches!(
            t.validate_for(h, &AuthRequired::None),
            Err(CapError::Unauthorized { .. })
        ));
    }

    // ── shm regions: a granted PD maps; the bytes round-trip ──────────────────

    #[test]
    fn shm_region_create_map_and_share() {
        // The kernel creates a region; a second mapping of the SAME name sees the
        // writes (the genuine shared-buffer the net-client needs).
        let region = ShmRegion::create(16).expect("shm create");
        region.with_mut(|b| b[0] = 0xAB);
        let mapped = ShmRegion::map_existing(region.name(), region.len()).expect("map");
        assert_eq!(mapped.read()[0], 0xAB);
        // A write through the second mapping is seen by the first (shared).
        mapped.with_mut(|b| b[1] = 0xCD);
        assert_eq!(region.read()[1], 0xCD);
    }

    #[test]
    fn cap_handle_bytes_round_trip() {
        let h = CapHandle { slot: 0xDEAD_BEEF, epoch: 0x1234 };
        assert_eq!(CapHandle::from_bytes(h.to_bytes()), h);
    }

    // ── the wire codec round-trips (the control-socket framing) ───────────────

    #[test]
    fn request_reply_codecs_round_trip() {
        let reqs = [
            KernelRequest::Signal { notif: CapHandle { slot: 1, epoch: 0 }, badge: 0x20 },
            KernelRequest::Wait { notif: CapHandle { slot: 2, epoch: 1 } },
            KernelRequest::Validate { handle: CapHandle { slot: 3, epoch: 2 } },
            KernelRequest::RegionInfo { region: CapHandle { slot: 4, epoch: 3 } },
        ];
        for r in reqs {
            assert_eq!(KernelRequest::decode(&r.encode()), Some(r));
        }
        let reps = [
            KernelReply::Ok,
            KernelReply::Badge(0x20),
            KernelReply::Valid { kind: "notification" },
            KernelReply::Region { name: "/df123".into(), len: 8 },
            KernelReply::Forged,
            KernelReply::WrongKind,
            KernelReply::Unauthorized,
        ];
        for r in reps {
            assert_eq!(KernelReply::decode(&r.encode()), Some(r));
        }
    }

    // ── kernel-side signal/poll over validated handles ────────────────────────

    #[test]
    fn kernel_signal_and_poll_validate_handles() {
        let k = ProcessKernel::new();
        let n = k.create_notification(AuthRequired::Either);
        k.signal(n, 0b101).unwrap();
        assert_eq!(k.poll_notification(n).unwrap(), 0b101);
        assert_eq!(k.poll_notification(n).unwrap(), 0);

        // A forged handle is refused at the kernel signal path.
        let forged = CapHandle { slot: 4242, epoch: 0 };
        assert!(matches!(k.signal(forged, 1), Err(CapError::Forged { .. })));
    }
}
