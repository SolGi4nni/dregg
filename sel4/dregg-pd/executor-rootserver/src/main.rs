//! executor-rootserver — STEP 4: the VERIFIED dregg executor running INSIDE an
//! seL4 protection domain.
//!
//! This raw seL4 root task hosts the verified executor closure
//! (`dregg_exec_full_forest_auth` = `execFullForestG` + admission, proved in
//! `metatheory/`). On boot it:
//!   1. installs an in-PD Linux-syscall handler via `sel4-musl` (the seL4/musllibc
//!      libc routes every syscall through the `__sysinfo` pointer this sets, so
//!      the Lean runtime's malloc/write/... are serviced here, NOT trapped to the
//!      kernel as seL4 syscalls);
//!   2. calls the C driver `dregg_rootserver_run_turn()` (scripts/driver-sel4.c),
//!      which runs the embedded-Lean init + ONE real turn through the verified
//!      executor and prints the receipt over the seL4 debug serial.
//!
//! The C side (the whole Lean runtime + the verified closure) is linked in as
//! archives rebuilt against the seL4 musl — see scripts/relink-roottask.sh and
//! Cargo's link wiring. `build.rs` emits the `cargo:rustc-link-*` lines.
//!
//! Modeled on the upstream reference
//! `~/sel4-sdk/rust-sel4/crates/private/tests/root-task/musl/src/main.rs`, here
//! driving the verified executor instead of `vec![1,2,3]`.

#![no_main]
#![allow(unreachable_patterns)]

use core::alloc::{GlobalAlloc, Layout};
use core::ffi::{c_char, c_int};
use core::ptr;

use one_shot_mutex::sync::RawOneShotMutex;

use sel4_dlmalloc::{StaticDlmalloc, StaticHeap};
use sel4_linux_syscall_types::{ENOMEM, ENOSYS, MAP_ANONYMOUS, SEEK_CUR};

// ENOENT (no such file/directory) — not re-exported by sel4-linux-syscall-types;
// the openat-probe path wants "not found" (recoverable), not ENOSYS (fatal).
const ENOENT: SyscallReturnValue = 2;
const EBADF: SyscallReturnValue = 9;

// The sentinel fd `openat("/dev/urandom")` returns; `read` zero-fills it. Chosen
// high so it never collides with stdio (0/1/2). The Lean runtime seeds its hash
// from /dev/urandom at init — it must open + read, so a real (if deterministic)
// fd is required, NOT ENOENT.
const URANDOM_FD: SyscallReturnValue = 1000;

/// True iff the NUL-terminated C string at `path_ptr` equals `want` (excluding
/// the NUL). Used to recognize `/dev/urandom` in openat without a libc.
fn path_is(path_ptr: *const u8, want: &[u8]) -> bool {
    if path_ptr.is_null() {
        return false;
    }
    for (i, &w) in want.iter().enumerate() {
        let c = unsafe { *path_ptr.add(i) };
        if c != w {
            return false;
        }
    }
    // the byte after `want` must be the NUL terminator (exact match)
    unsafe { *path_ptr.add(want.len()) == 0 }
}
use sel4_musl::{
    ParseSyscallError, Syscall, SyscallReturnValue, VaListAsSyscallArgs, set_syscall_handler,
};
use sel4_root_task_with_std::{debug_print, debug_println, declare_root_task};

declare_root_task!(main = main);

// The C driver that runs ONE verified turn (scripts/driver-sel4.c). Returns 0 on
// the turn completing (a receipt was produced); nonzero on a runtime init error.
unsafe extern "C" {
    fn dregg_rootserver_run_turn() -> c_int;
}

// THE ORDERING FIX (WALL-roottask.md §"the __sysinfo-null fault"): the seL4 musl
// libc routes every syscall through the `__sysinfo` function pointer, NULL until
// `set_syscall_handler` populates it. But `sel4-runtime-common`'s `global_init()`
// runs the C++ `.init_array` constructors (libstdc++/Lean static initializers —
// 7 of them) BEFORE our `main`, and at least one allocates (malloc → mmap →
// `br __sysinfo`(=0) → instruction fault at address 0, the "vm fault on code at
// address 0" the first boot hit). The rust-sel4 ctor runner executes
// `.preinit_array` BEFORE `.init_array` (`sel4_ctors_dtors::run_ctors`), so a
// `.preinit_array` entry installs the handler ahead of every C++ ctor.
unsafe extern "C" fn install_syscall_handler_preinit() {
    unsafe {
        set_syscall_handler(handle_syscall);
    }
}

#[used]
#[unsafe(link_section = ".preinit_array")]
static PREINIT_INSTALL_SYSCALL_HANDLER: unsafe extern "C" fn() =
    install_syscall_handler_preinit;

fn main(_: &sel4::BootInfoPtr) -> ! {
    // The syscall handler is ALREADY installed by the .preinit_array hook above
    // (ahead of the C++ ctors). We must NOT set it again here:
    // `ImmediateSyncOnceCell` panics on a second `set`.

    debug_println!("");
    debug_println!("    ┌─────────────────────────────────────────────────────┐");
    debug_println!("    │  dregg executor-rootserver · the VERIFIED turn on    │");
    debug_println!("    │  seL4 (execFullForestG inside a protection domain)   │");
    debug_println!("    └─────────────────────────────────────────────────────┘");
    debug_println!("");
    debug_println!("[rootserver] seL4 root task booted; sel4-musl syscall handler installed");
    debug_println!("[rootserver] >>> running ONE verified turn through dregg_exec_full_forest_auth");
    debug_println!("");

    let rc = unsafe { dregg_rootserver_run_turn() };

    debug_println!("");
    if rc == 0 {
        debug_println!("[rootserver] <<< turn complete — the VERIFIED executor ran INSIDE seL4 ( ◕‿◕ )");
    } else {
        debug_println!("[rootserver] <<< runtime init returned rc={rc} (see receipt/log above)");
    }

    // A root task may not return; park.
    sel4::init_thread::suspend_self()
}

/// The in-PD Linux-syscall handler. Covers the surface the embedded Lean runtime
/// exercises on the pure executor turn: heap (Brk + anonymous Mmap), stdout/stderr
/// (Write/Writev), and the no-op identity calls (getuid/lseek). Any syscall the
/// turn unexpectedly reaches is reported (panic) rather than silently faked — an
/// unknown syscall is a precise next wall to characterize, not something to fudge.
fn handle_syscall(
    syscall: Result<Syscall, ParseSyscallError<VaListAsSyscallArgs>>,
) -> SyscallReturnValue {
    match syscall {
        Ok(syscall) => handle_known_syscall(syscall),
        // The `sel4-linux-syscall-types` parser only recognizes a handful of
        // syscalls (Brk/Mmap/Write/...); everything else arrives here by raw
        // number. The embedded Lean runtime + musl/libstdc++ startup make several
        // syscalls beyond the upstream minimal test's surface — handled by aarch64
        // syscall number below. On a single seL4 PD with no signals, no other
        // threads contending, and no real clock/RNG need for the deterministic
        // verified turn, the faithful answers are no-op success / zero-fill.
        Err(ParseSyscallError::UnrecognizedSyscallNumber { sysnum, args }) => {
            handle_by_number(sysnum, args)
        }
        Err(err) => {
            debug_println!("[rootserver] UNPARSED SYSCALL (a precise wall): {err:?}");
            -ENOSYS
        }
    }
}

// aarch64 Linux syscall numbers (asm-generic, the musl aarch64 ABI).
mod nr {
    use sel4_linux_syscall_types::SyscallNumber;
    pub const IOCTL: SyscallNumber = 29;
    pub const FUTEX: SyscallNumber = 98;
    pub const SET_ROBUST_LIST: SyscallNumber = 99;
    pub const NANOSLEEP: SyscallNumber = 101;
    pub const CLOCK_GETTIME: SyscallNumber = 113;
    pub const SCHED_GETAFFINITY: SyscallNumber = 123;
    pub const SIGALTSTACK: SyscallNumber = 132;
    pub const RT_SIGACTION: SyscallNumber = 134;
    pub const RT_SIGPROCMASK: SyscallNumber = 135;
    pub const SET_TID_ADDRESS: SyscallNumber = 96;
    pub const MPROTECT: SyscallNumber = 226;
    pub const MADVISE: SyscallNumber = 233;
    pub const PRLIMIT64: SyscallNumber = 261;
    pub const GETRANDOM: SyscallNumber = 278;
    pub const TGKILL: SyscallNumber = 131;
    pub const EXIT_GROUP: SyscallNumber = 94;
    pub const RSEQ: SyscallNumber = 293;
    pub const MEMBARRIER: SyscallNumber = 283;
    // File-I/O the Lean module-init import chain probes (the verified TURN reads
    // no files; init's stdio/env probes should see "not found" and move on).
    pub const OPENAT: SyscallNumber = 56;
    pub const CLOSE: SyscallNumber = 57;
    pub const READ: SyscallNumber = 63;
    pub const FCNTL: SyscallNumber = 25;
    pub const FSTAT: SyscallNumber = 80;
    pub const NEWFSTATAT: SyscallNumber = 79;
    pub const READLINKAT: SyscallNumber = 78;
    pub const FACCESSAT: SyscallNumber = 48;
    pub const STATX: SyscallNumber = 291;
    pub const PPOLL: SyscallNumber = 73;
    pub const GETPID: SyscallNumber = 172;
    pub const GETTID: SyscallNumber = 178;
    pub const GETRUSAGE: SyscallNumber = 165;
    pub const SYSINFO: SyscallNumber = 179;
    pub const SCHED_YIELD: SyscallNumber = 124;
}

/// Handle the syscalls the Lean/musl/libstdc++ startup reaches that the parser
/// doesn't name. The verified turn is pure + single-threaded + deterministic, so:
///   * signal/thread-id/robust-list/rseq/membarrier setup → no-op success (0)
///   * mprotect/madvise (the GC + mmap arenas already mapped by our Mmap) → 0
///   * futex (no contention in a single PD) → 0
///   * clock_gettime → zero the timespec, return 0 (the turn uses no real time)
///   * getrandom → zero-fill (deterministic; the turn's crypto floor is the
///     Rust-PD-supplied stub, not reached on a non-crypto turn — see crypto-stub)
///   * exit_group → the turn is done; loop (the PD's main handles teardown)
fn handle_by_number(sysnum: sel4_linux_syscall_types::SyscallNumber, mut args: VaListAsSyscallArgs) -> SyscallReturnValue {
    use sel4_linux_syscall_types::SyscallArgs;
    match sysnum {
        nr::SET_TID_ADDRESS | nr::SET_ROBUST_LIST | nr::RT_SIGACTION | nr::RT_SIGPROCMASK
        | nr::SIGALTSTACK | nr::IOCTL | nr::MPROTECT | nr::MADVISE | nr::PRLIMIT64
        | nr::SCHED_GETAFFINITY | nr::RSEQ | nr::MEMBARRIER | nr::TGKILL | nr::NANOSLEEP => 0,
        nr::FUTEX => 0, // uncontended in a single PD
        nr::GETPID | nr::GETTID => 1, // a single PD: pid/tid = 1
        nr::SCHED_YIELD | nr::PPOLL | nr::GETRUSAGE | nr::SYSINFO => 0,
        // openat: the Lean runtime init opens `/dev/urandom` to seed its hashing
        // (and may probe other paths). `/dev/urandom` MUST open + read (it is
        // fatal-if-missing for init); we give it a sentinel fd (URANDOM_FD) that
        // `read` zero-fills (deterministic — the verified turn's actual crypto is
        // the Rust-PD-supplied floor, not /dev/urandom). Any OTHER path → ENOENT
        // (recoverable "not found"; the turn reads no real file).
        nr::OPENAT => {
            let _dirfd: usize = args.next_arg().unwrap_or(0);
            let path_ptr: *const u8 = args.next_arg::<usize>().unwrap_or(0) as *const u8;
            if path_is(path_ptr, b"/dev/urandom") || path_is(path_ptr, b"/dev/random") {
                URANDOM_FD
            } else {
                -ENOENT
            }
        }
        nr::FACCESSAT | nr::READLINKAT | nr::STATX | nr::NEWFSTATAT => -ENOENT,
        nr::CLOSE | nr::FCNTL => 0,
        // read: on the /dev/urandom sentinel fd, zero-fill `count` bytes
        // (deterministic randomness for the init seed). On any other fd, EOF.
        nr::READ => {
            let fd: SyscallReturnValue = args.next_arg::<usize>().unwrap_or(0) as SyscallReturnValue;
            let buf: *mut u8 = args.next_arg::<usize>().unwrap_or(0) as *mut u8;
            let count: usize = args.next_arg().unwrap_or(0);
            if fd == URANDOM_FD && !buf.is_null() {
                for i in 0..count {
                    unsafe { buf.add(i).write(0) };
                }
                count as SyscallReturnValue
            } else {
                0 // EOF
            }
        }
        nr::FSTAT => -EBADF,
        nr::CLOCK_GETTIME => {
            // args: (clockid, *timespec). Zero the timespec (tv_sec, tv_nsec).
            let _clockid: usize = args.next_arg().unwrap_or(0);
            let ts: *mut u64 = args.next_arg::<usize>().unwrap_or(0) as *mut u64;
            if !ts.is_null() {
                unsafe {
                    ts.write(0);
                    ts.add(1).write(0);
                }
            }
            0
        }
        nr::GETRANDOM => {
            // args: (*buf, buflen, flags). Zero-fill deterministically.
            let buf: *mut u8 = args.next_arg::<usize>().unwrap_or(0) as *mut u8;
            let len: usize = args.next_arg().unwrap_or(0);
            if !buf.is_null() {
                for i in 0..len {
                    unsafe { buf.add(i).write(0) };
                }
            }
            len as SyscallReturnValue
        }
        nr::EXIT_GROUP => {
            debug_println!("[rootserver] (libc exit_group during/after the turn — parking)");
            sel4::init_thread::suspend_self()
        }
        other => {
            debug_println!("[rootserver] UNHANDLED SYSCALL number {other} (a precise wall)");
            -ENOSYS
        }
    }
}

fn handle_known_syscall(syscall: Syscall) -> SyscallReturnValue {
    use Syscall::*;

    match syscall {
        Getuid | Geteuid | Getgid | Getegid => 0,
        Brk { addr } => {
            let bounds = BRK_HEAP.bounds();
            (if addr.is_null() {
                bounds.start()
            } else if (bounds.start()..bounds.end()).contains(&addr.cast()) {
                addr.cast()
            } else {
                ptr::null()
            }) as SyscallReturnValue
        }
        Mmap {
            addr: _,
            len,
            prot: _,
            flag,
            fd: _,
            offset: _,
        } => {
            if flag & MAP_ANONYMOUS != 0 {
                (unsafe { MMAP_DLMALLOC.alloc(Layout::from_size_align(len, 4096).unwrap()) })
                    as SyscallReturnValue
            } else {
                -ENOMEM
            }
        }
        Lseek { fd, offset, whence } => {
            assert!(whence == SEEK_CUR);
            assert!(offset == 0);
            assert!((0..=2).contains(&fd));
            0
        }
        Write { fd, buf, count } => {
            assert!(fd == 1 || fd == 2);
            for i in 0..(count as isize) {
                let c: c_char = unsafe { *buf.offset(i) };
                debug_print!("{}", c as u8 as char);
            }
            count as SyscallReturnValue
        }
        Writev { fd, iov, iovcnt } => {
            assert!(fd == 1 || fd == 2);
            let mut ret: isize = 0;
            for i in 0..(iovcnt as isize) {
                let iov = unsafe { &*iov.offset(i) };
                for j in 0..(iov.iov_len as isize) {
                    let c: u8 = unsafe { *(iov.iov_base as *const u8).offset(j) };
                    debug_print!("{}", c as char);
                    ret += 1;
                }
            }
            ret as SyscallReturnValue
        }
        // Any other syscall the verified turn reaches is a precise wall: report
        // it (with its number, via Debug) and fail-closed with -ENOSYS so the
        // libc path surfaces the exact gap rather than the PD faking a result.
        other => {
            debug_println!("[rootserver] UNHANDLED SYSCALL (a precise wall): {other:?}");
            -ENOSYS
        }
    }
}

// The brk heap and the mmap pool. The Lean runtime + the one transfer turn fit in
// a few MiB (the host-musl run's RSS is modest); sized generously for the GC
// arena. These are static PD memory (the root task's own frames).
static BRK_HEAP: StaticHeap<{ 4 * 1024 * 1024 }> = StaticHeap::new();

const MMAP_HEAP_SIZE: usize = 64 * 1024 * 1024;
static MMAP_HEAP: StaticHeap<MMAP_HEAP_SIZE> = StaticHeap::new();
static MMAP_DLMALLOC: StaticDlmalloc<RawOneShotMutex> = StaticDlmalloc::new(MMAP_HEAP.bounds());
