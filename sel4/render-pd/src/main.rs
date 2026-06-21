//! render-PD — the lavapipe software-Vulkan ICD (and, on top of it, the
//! gpui-offscreen cockpit render) running INSIDE a seL4 protection domain, so
//! the cockpit RE-FLOWS live per-frame instead of blitting one baked
//! `cockpit_frame.rgba`.
//!
//! This is the `executor-rootserver` PD class: a raw seL4 root task on
//! `sel4-root-task-with-std` + `sel4-musl`, NOT the `#![no_std]` microkit
//! deos-image PD. The difference from executor-rootserver is WHAT the PD hosts:
//! instead of the verified Lean closure it links the lavapipe ICD
//! (`out/mesa-elf/libvulkan_lvp.so`, built by `scripts/build-mesa-lavapipe-elf.sh`
//! — a real aarch64-musl software-Vulkan driver that JITs shaders through static
//! LLVM 20.1.8) and drives a render through it.
//!
//! On boot it:
//!   1. installs an in-PD Linux-syscall handler via `sel4-musl` (a `.preinit_array`
//!      hook, ahead of every C++ ctor — the executor PD's ordering fix);
//!   2. calls the C driver `dregg_render_pd_run()` (scripts/driver-render.c),
//!      which resolves the ICD LOADER-LESS (`vk_icdGetInstanceProcAddr`, never the
//!      static `vkXxx` symbols), creates a Vulkan instance, enumerates the
//!      llvmpipe `VkPhysicalDevice`, and — crucially — drives the path that JITs
//!      (so the LLVM ORC/MCJIT exercises its W→X executable mapping, the ONE
//!      genuinely new OS demand vs the executor PD). It prints what it observed
//!      over the seL4 debug serial.
//!
//! ## THE ONE NEW OS DEMAND: the JIT's W→X executable mapping
//!
//! llvmpipe JITs each shader: it mmaps an anonymous RW region, writes machine
//! code into it, then makes it executable (`mprotect(PROT_EXEC)` or an
//! `mmap(PROT_READ|WRITE|EXEC)` arena). The executor PD never JITs, so this is the
//! one syscall surface it never exercised. We service it WITHOUT a new seL4
//! capability, because the `aarch64-sel4-roottask-musl` target links
//! `--no-rosegment` (target spec) → the seL4 kernel maps the WHOLE root-task image
//! as one combined loadable with execute permission (the same property that lets
//! the root task's own `.text` run). So a static byte arena that lives in the
//! image is itself executable. The handler serves every executable mmap/mprotect
//! request out of that static RWX arena (`JIT_ARENA` below). See `WIRING.md`.
//!
//! ## LP_NUM_THREADS=0 — single-threaded llvmpipe (no thread infra)
//!
//! `getenv("LP_NUM_THREADS")` returns `"0"` from the in-PD `environ`, so llvmpipe
//! runs its rasterizer single-threaded — no `pthread_create`, no rasterizer pool,
//! no futex contention. This matches the executor PD's single-thread profile and
//! sidesteps thread-spawn entirely.

#![no_main]
#![allow(unreachable_patterns)]

use core::alloc::{GlobalAlloc, Layout};
use core::ffi::{c_char, c_int};
use core::ptr;

use one_shot_mutex::sync::RawOneShotMutex;

use sel4_dlmalloc::{StaticDlmalloc, StaticHeap};
use sel4_linux_syscall_types::{ENOMEM, ENOSYS, MAP_ANONYMOUS, SEEK_CUR};

// ENOENT (no such file/directory) — the openat-probe path wants "not found"
// (recoverable), not ENOSYS (fatal).
const ENOENT: SyscallReturnValue = 2;
const EBADF: SyscallReturnValue = 9;

// The sentinel fd `openat("/dev/urandom")` returns; `read` zero-fills it. lavapipe
// touches no /dev/urandom directly, but the musl/libstdc++ startup may, so keep
// the executor PD's deterministic answer.
const URANDOM_FD: SyscallReturnValue = 1000;

// The sentinel fd `openat("/proc/cpuinfo")` returns. lavapipe's LLVM JIT
// (`lp_build_create_jit_compiler_for_module` → `sys::getHostCPUName` +
// `getHostCPUFeatures`) reads `/proc/cpuinfo` to pick the host CPU + feature flags.
// With NO cpuinfo it returns an empty CPU name + empty feature map, and the
// downstream EngineBuilder/target-select then faults (measured: a NULL deref right
// after LLVM's "Can't read /proc/cpuinfo"). We serve a faithful aarch64
// (cortex-a53 — the QEMU `-cpu cortex-a53` we boot) cpuinfo so the JIT gets a real
// host description: `CPU implementer 0x41` (ARM) + `CPU part 0xd03` (Cortex-A53) →
// `getHostCPUName` returns "cortex-a53"; the `Features:` line drives the MAttrs.
const CPUINFO_FD: SyscallReturnValue = 1001;

/// The synthetic /proc/cpuinfo (one cortex-a53 core; the QEMU cpu we boot). The
/// `Features:` keywords map (LLVM `getHostCPUFeatures`): fp→fp-armv8, asimd→neon,
/// etc. `CPU implementer/part` let `getHostCPUNameForARM` resolve "cortex-a53".
const CPUINFO: &[u8] = b"processor\t: 0\n\
BogoMIPS\t: 100.00\n\
Features\t: fp asimd evtstrm aes pmull sha1 sha2 crc32\n\
CPU implementer\t: 0x41\n\
CPU architecture: 8\n\
CPU variant\t: 0x0\n\
CPU part\t: 0xd03\n\
CPU revision\t: 4\n\n";

/// Per-fd read cursor for the synthetic /proc/cpuinfo (single-threaded reads of it;
/// the JIT reads it once during device creation).
static CPUINFO_CURSOR: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);

// PROT_* (the musl/Linux aarch64 mmap protection bits). sel4-linux-syscall-types
// gives MAP_ANONYMOUS; the PROT bits we read off the raw Mmap/Mprotect args.
const PROT_EXEC: usize = 0x4;

/// True iff the NUL-terminated C string at `path_ptr` equals `want`.
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
    unsafe { *path_ptr.add(want.len()) == 0 }
}

use sel4_musl::{
    ParseSyscallError, Syscall, SyscallReturnValue, VaListAsSyscallArgs, set_syscall_handler,
};
use sel4_root_task_with_std::{debug_print, debug_println, declare_root_task};

// The final rung — RGBA (from the in-PD lavapipe render) → XRGB8888 → the PD
// framebuffer. LIVE on the boot path: `main` reads the driver's staged RGBA
// (`dregg_render_pd_rgba`, written by driver-render.c STAGE 5) and drives
// `render_blit::blit_rgba_to_framebuffer` into `PD_FRAMEBUFFER` below. (The
// PD-owned static framebuffer stands in for the ramfb scanout region until the
// device-cap fb mapping lands — the seam render_blit.rs documents; the
// RGBA→XRGB8888 blit itself is exercised for real here.)
mod render_blit;

// Real seL4 thread bring-up: services musl's `__clone` (which lavapipe's
// `lvp_queue_init` reaches via `thrd_create`) by materializing a second seL4 TCB.
// The seL4-musl `__clone` is a `-ENOSYS` stub; `musl-compat.c` overrides it (link
// precedence) to call `thread::dregg_clone`. See `src/thread.rs` + WIRING.md.
mod thread;

declare_root_task!(main = main);

// The C driver that drives one lavapipe smoke (scripts/driver-render.c). Returns
// 0 if the ICD created an instance + enumerated the llvmpipe device (and, when
// wired, JIT'd + rendered); nonzero with a stage code otherwise.
unsafe extern "C" {
    fn dregg_render_pd_run() -> c_int;
    // The in-PD lavapipe render staging buffer (driver-render.c STAGE 5):
    // dregg_render_pd_render rasterizes one 800×600 RGBA frame into it; these
    // accessors expose it to the Rust render_blit weld.
    fn dregg_render_pd_rgba() -> *const u8;
    fn dregg_render_pd_rgba_len() -> usize;
    fn dregg_render_pd_rgba_ready() -> c_int;
    fn dregg_render_pd_rgba_checksum() -> u32;
}

// ───────────────────── the PD-owned framebuffer (ramfb stand-in) ─────────────
//
// The XRGB8888 surface render_blit blits into. In the deos-image PD this is the
// fw_cfg/ramfb-mapped scanout region; in this raw root task the device-cap fb
// mapping is a separate OS rung (render_blit.rs §"the framebuffer-mapping half"),
// so the blit's RECEIVING end is this PD-owned static buffer — exercising the
// real RGBA→XRGB8888 conversion. Wiring it to the ramfb scanout frames is the
// thin device-cap seam on top (same "give the root task the device caps" rung as
// the `__clone` TCB work).
const FB_PIXELS: usize = (render_blit::WIDTH * render_blit::HEIGHT) as usize;
#[used]
static mut PD_FRAMEBUFFER: [u32; FB_PIXELS] = [0u32; FB_PIXELS];

/// FNV-1a over the XRGB8888 framebuffer's RGB (matching the C side's RGBA FNV-1a
/// over the source bytes is NOT identical — different inputs; this is the blit's
/// OWN output checksum, printed so the serial shows the blit ran and produced a
/// stable result, and so a regression changes it).
fn fb_checksum(fb: &[u32]) -> u32 {
    let mut h: u32 = 2166136261;
    for &px in fb {
        for b in [(px >> 16) as u8, (px >> 8) as u8, px as u8] {
            h ^= b as u32;
            h = h.wrapping_mul(16777619);
        }
    }
    h
}

/// THE RENDER WELD (Rust half): take the driver's in-PD-rendered RGBA and blit it
/// RGBA→XRGB8888 into the PD framebuffer via the LIVE `render_blit`. Returns the
/// pixel count written (0 if no frame / a geometry mismatch — render_blit's
/// fail-closed contract). Prints the C-side source checksum + the blit's own
/// output checksum so the serial witnesses the bytes flowed end to end.
fn weld_render_to_framebuffer() -> usize {
    let ready = unsafe { dregg_render_pd_rgba_ready() } != 0;
    if !ready {
        debug_println!("[render-pd] no in-PD frame staged (render STAGE 5 did not complete) — framebuffer left blank");
        return 0;
    }
    let len = unsafe { dregg_render_pd_rgba_len() };
    let ptr = unsafe { dregg_render_pd_rgba() };
    if ptr.is_null() || len == 0 {
        debug_println!("[render-pd] staged RGBA is empty — framebuffer left blank");
        return 0;
    }
    let rgba: &[u8] = unsafe { core::slice::from_raw_parts(ptr, len) };
    let fb: &mut [u32] = unsafe { &mut *core::ptr::addr_of_mut!(PD_FRAMEBUFFER) };
    let written = render_blit::blit_rgba_to_framebuffer(rgba, fb);
    let src_sum = unsafe { dregg_render_pd_rgba_checksum() };
    debug_println!(
        "[render-pd] render_blit: {written} px RGBA->XRGB8888 (src RGBA fnv=0x{src_sum:08x}, fb out fnv=0x{:08x})",
        fb_checksum(fb)
    );
    written
}

// THE ORDERING FIX (executor-rootserver WALL-roottask.md §"the __sysinfo-null
// fault"): install the syscall handler in `.preinit_array`, ahead of the C++
// `.init_array` ctors (libstdc++/LLVM static initializers), at least one of which
// allocates → mmap → `br __sysinfo`(=0) instruction fault if the handler isn't up.
unsafe extern "C" fn install_syscall_handler_preinit() {
    unsafe {
        set_syscall_handler(handle_syscall);
    }
}

#[used]
#[unsafe(link_section = ".preinit_array")]
static PREINIT_INSTALL_SYSCALL_HANDLER: unsafe extern "C" fn() =
    install_syscall_handler_preinit;

fn main(bootinfo: &sel4::BootInfoPtr) -> ! {
    // Handler already installed by the .preinit_array hook above.
    //
    // CAPTURE the BootInfo for the seL4 thread bring-up: `thread::dregg_clone`
    // (servicing lavapipe's submit-thread `__clone`) retypes a TCB from an untyped
    // and resolves its IPC-buffer frame cap — both reached through this BootInfo.
    // The BootInfo lives for the whole program, so the 'static is sound.
    let bootinfo_static: &'static sel4::BootInfo =
        unsafe { &*(&**bootinfo as *const sel4::BootInfo) };
    thread::init(bootinfo_static);
    //
    // THE SINGLE-THREAD LEVER is supplied by the compat shim's `getenv` override
    // (scripts/musl-compat.c): it returns "0" for LP_NUM_THREADS so llvmpipe runs
    // its rasterizer single-threaded — no `thrd_create`, no rasterizer pool. On
    // this single-core seL4 PD there IS no second thread to schedule, so a >0
    // thread count had lavapipe spin a rasterizer pool that cannot run (the
    // observed `vkCreateDevice = VK_ERROR_UNKNOWN`). We do NOT use
    // `std::env::set_var` here: this minimal root task has a NULL `environ`, so
    // touching std's env machinery faults at address 0 before main — the getenv
    // override sidesteps `environ` entirely.

    debug_println!("");
    debug_println!("    ┌─────────────────────────────────────────────────────┐");
    debug_println!("    │  dregg render-PD · lavapipe software-Vulkan + the    │");
    debug_println!("    │  gpui-offscreen cockpit render INSIDE seL4           │");
    debug_println!("    └─────────────────────────────────────────────────────┘");
    debug_println!("");
    debug_println!("[render-pd] seL4 root task booted; sel4-musl syscall handler installed");
    debug_println!(
        "[render-pd] JIT W->X arena: {} KiB static RWX (--no-rosegment image)",
        JIT_ARENA_SIZE / 1024
    );
    debug_println!("[render-pd] >>> driving the lavapipe ICD (loader-less vk_icdGetInstanceProcAddr)");
    debug_println!("");

    let rc = unsafe { dregg_render_pd_run() };

    // THE RENDER WELD: blit the in-PD-rendered RGBA → XRGB8888 → the PD
    // framebuffer (render_blit, now live on the boot path, not dead code).
    debug_println!("");
    debug_println!("[render-pd] >>> render_blit weld: in-PD RGBA -> XRGB8888 -> PD framebuffer");
    let blit_px = weld_render_to_framebuffer();
    let want_px = FB_PIXELS;
    if blit_px == want_px {
        debug_println!("[render-pd] render_blit OK — {blit_px} px on the PD framebuffer (a real in-VM frame, not the bake)");
    } else {
        debug_println!("[render-pd] render_blit wrote {blit_px}/{want_px} px (no frame or geometry mismatch — fail-closed)");
    }

    debug_println!("");
    if rc == 0 {
        debug_println!("[render-pd] <<< lavapipe ran INSIDE seL4 — software Vulkan on glass ( ◕‿◕ )");
    } else {
        debug_println!("[render-pd] <<< driver returned rc={rc} (a precise stage code — see above)");
    }

    sel4::init_thread::suspend_self()
}

/// The in-PD Linux-syscall handler. Covers the executor PD's surface PLUS
/// lavapipe's two additions: the JIT's W→X executable mmap/mprotect (serviced
/// from the static RWX arena) and `getenv` (LP_NUM_THREADS=0 + the ICD env, read
/// from `environ` the C runtime already exposes; no syscall needed for getenv).
fn handle_syscall(
    syscall: Result<Syscall, ParseSyscallError<VaListAsSyscallArgs>>,
) -> SyscallReturnValue {
    match syscall {
        Ok(syscall) => handle_known_syscall(syscall),
        Err(ParseSyscallError::UnrecognizedSyscallNumber { sysnum, args }) => {
            handle_by_number(sysnum, args)
        }
        Err(err) => {
            debug_println!("[render-pd] UNPARSED SYSCALL (a precise wall): {err:?}");
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
    pub const MMAP: SyscallNumber = 222;
    pub const MUNMAP: SyscallNumber = 215;
    pub const MPROTECT: SyscallNumber = 226;
    pub const MADVISE: SyscallNumber = 233;
    pub const PRLIMIT64: SyscallNumber = 261;
    pub const GETRANDOM: SyscallNumber = 278;
    pub const TGKILL: SyscallNumber = 131;
    pub const EXIT: SyscallNumber = 93;
    pub const EXIT_GROUP: SyscallNumber = 94;
    pub const RSEQ: SyscallNumber = 293;
    pub const MEMBARRIER: SyscallNumber = 283;
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

/// Handle syscalls reached by raw number. The executor PD's faithful answers,
/// PLUS the JIT-mapping additions.
fn handle_by_number(
    sysnum: sel4_linux_syscall_types::SyscallNumber,
    mut args: VaListAsSyscallArgs,
) -> SyscallReturnValue {
    use sel4_linux_syscall_types::SyscallArgs;
    match sysnum {
        // ───────── THE JIT W→X MAPPING — the one genuinely new OS demand ──────
        //
        // llvmpipe JITs shaders: it asks for an executable mapping. We serve it
        // out of the static RWX arena (JIT_ARENA), which is executable because
        // the root-task image is mapped with execute permission (--no-rosegment;
        // see the module doc). Two shapes reach here:
        //
        //   * mmap(PROT_READ|WRITE|EXEC, MAP_ANONYMOUS) — the ORC/JITLink memory
        //     manager reserving an executable code arena up front. We hand back a
        //     run of the RWX arena, so the bytes the JIT writes there are
        //     immediately runnable (W and X coexist — the simplest faithful W→X).
        //   * mmap(PROT_READ|WRITE) then mprotect(..., PROT_EXEC) — the classic
        //     SectionMemoryManager W→X flip. The initial mmap (RW, no exec) is
        //     served by the ordinary anon path (MMAP_DLMALLOC); the later
        //     mprotect(PROT_EXEC) must make THAT region executable. Since the anon
        //     pool (MMAP_HEAP) is itself in the RWX image, the region is ALREADY
        //     executable — so mprotect(PROT_EXEC) is a no-op success (0). The
        //     execute bit was never absent; --no-rosegment gives the whole image
        //     X. We log the PROT_EXEC flip so the W→X path is observable.
        nr::MMAP => {
            let _addr: usize = args.next_arg().unwrap_or(0);
            let len: usize = args.next_arg().unwrap_or(0);
            let prot: usize = args.next_arg().unwrap_or(0);
            let flag: usize = args.next_arg().unwrap_or(0);
            let _fd: usize = args.next_arg().unwrap_or(0);
            let _off: usize = args.next_arg().unwrap_or(0);
            if flag & (MAP_ANONYMOUS as usize) == 0 {
                return -ENOMEM; // file-backed mmap: not serviced (no fs)
            }
            if prot & PROT_EXEC != 0 {
                // Executable arena: serve from the static RWX JIT arena.
                match jit_arena_alloc(len) {
                    Some(p) => {
                        JIT_EXEC_MAPS.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
                        p as SyscallReturnValue
                    }
                    None => {
                        debug_println!(
                            "[render-pd] JIT arena EXHAUSTED on exec mmap({} KiB) — grow JIT_ARENA_SIZE",
                            len / 1024
                        );
                        -ENOMEM
                    }
                }
            } else {
                // Ordinary RW anon mmap — from the general pool (itself RWX-image,
                // so a later mprotect(PROT_EXEC) on it is a no-op).
                (unsafe { MMAP_DLMALLOC.alloc(Layout::from_size_align(len.max(1), 4096).unwrap()) })
                    as SyscallReturnValue
            }
        }
        nr::MPROTECT => {
            // args: (addr, len, prot). The W→X flip: a region the JIT wrote code
            // into is being made executable. The whole image is already X
            // (--no-rosegment), so the page-level execute bit is present — this is
            // a faithful no-op success. Count the PROT_EXEC flips so W→X is visible.
            let _addr: usize = args.next_arg().unwrap_or(0);
            let _len: usize = args.next_arg().unwrap_or(0);
            let prot: usize = args.next_arg().unwrap_or(0);
            if prot & PROT_EXEC != 0 {
                JIT_WX_FLIPS.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
            }
            0
        }
        nr::MUNMAP => 0, // the static arenas are never returned to the kernel; no-op

        // ───────── the executor PD's faithful answers (unchanged) ────────────
        nr::SET_TID_ADDRESS | nr::SET_ROBUST_LIST | nr::RT_SIGACTION | nr::RT_SIGPROCMASK
        | nr::SIGALTSTACK | nr::IOCTL | nr::MADVISE | nr::PRLIMIT64
        | nr::SCHED_GETAFFINITY | nr::RSEQ | nr::MEMBARRIER | nr::TGKILL | nr::NANOSLEEP => 0,
        nr::FUTEX => 0, // uncontended: LP_NUM_THREADS=0 ⇒ single-threaded rasterizer
        nr::GETPID | nr::GETTID => 1,
        nr::SCHED_YIELD | nr::PPOLL | nr::GETRUSAGE | nr::SYSINFO => 0,
        nr::OPENAT => {
            let _dirfd: usize = args.next_arg().unwrap_or(0);
            let path_ptr: *const u8 = args.next_arg::<usize>().unwrap_or(0) as *const u8;
            if path_is(path_ptr, b"/dev/urandom") || path_is(path_ptr, b"/dev/random") {
                URANDOM_FD
            } else if path_is(path_ptr, b"/proc/cpuinfo") {
                CPUINFO_CURSOR.store(0, core::sync::atomic::Ordering::Relaxed);
                CPUINFO_FD
            } else {
                -ENOENT
            }
        }
        nr::FACCESSAT | nr::READLINKAT | nr::STATX | nr::NEWFSTATAT => -ENOENT,
        nr::CLOSE | nr::FCNTL => 0,
        nr::READ => {
            let fd: SyscallReturnValue = args.next_arg::<usize>().unwrap_or(0) as SyscallReturnValue;
            let buf: *mut u8 = args.next_arg::<usize>().unwrap_or(0) as *mut u8;
            let count: usize = args.next_arg().unwrap_or(0);
            if fd == URANDOM_FD && !buf.is_null() {
                for i in 0..count {
                    unsafe { buf.add(i).write(0) };
                }
                count as SyscallReturnValue
            } else if fd == CPUINFO_FD && !buf.is_null() {
                use core::sync::atomic::Ordering;
                let pos = CPUINFO_CURSOR.load(Ordering::Relaxed);
                let remaining = CPUINFO.len().saturating_sub(pos);
                let n = remaining.min(count);
                for i in 0..n {
                    unsafe { buf.add(i).write(CPUINFO[pos + i]) };
                }
                CPUINFO_CURSOR.store(pos + n, Ordering::Relaxed);
                n as SyscallReturnValue
            } else {
                0
            }
        }
        nr::FSTAT => -EBADF,
        nr::CLOCK_GETTIME => {
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
            let buf: *mut u8 = args.next_arg::<usize>().unwrap_or(0) as *mut u8;
            let len: usize = args.next_arg().unwrap_or(0);
            if !buf.is_null() {
                for i in 0..len {
                    unsafe { buf.add(i).write(0) };
                }
            }
            len as SyscallReturnValue
        }
        nr::EXIT => {
            // A pthread tearing down: musl's `__pthread_exit` ends in `exit(93)`.
            // Suspend the CALLING seL4 thread (identified by its TPIDR_EL0), NOT the
            // whole PD — a secondary (e.g. the lavapipe submit) thread exiting must
            // not take down the render. If the caller is the main thread, this parks
            // the PD (its `exit` is the process exit).
            thread::suspend_current_thread()
        }
        nr::EXIT_GROUP => {
            debug_println!("[render-pd] (libc exit_group during/after the render — parking)");
            sel4::init_thread::suspend_self()
        }
        220 => {
            // CLONE by raw number — if pthread_create issues SYS_clone via __syscall
            // (rather than the __clone asm we override), service it here.
            debug_println!("[render-pd] CLONE syscall (#220) reached handle_by_number");
            let fn_: usize = args.next_arg().unwrap_or(0);
            let stack: usize = args.next_arg().unwrap_or(0);
            let flags: usize = args.next_arg().unwrap_or(0);
            let arg: usize = args.next_arg().unwrap_or(0);
            unsafe { thread::dregg_clone(fn_, stack, flags, arg, 0, 0, 0) as SyscallReturnValue }
        }
        other => {
            debug_println!("[render-pd] UNHANDLED SYSCALL number {other} (a precise wall)");
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
            prot,
            flag,
            fd: _,
            offset: _,
        } => {
            if flag & MAP_ANONYMOUS == 0 {
                return -ENOMEM;
            }
            // THE JIT W→X path through the PARSED Mmap (the parser DOES name Mmap).
            // An executable anon mmap → the RWX JIT arena; otherwise the general
            // anon pool. (Mirrors the raw-number MMAP arm above; whichever path the
            // libc takes, the executable mapping comes from RWX memory.)
            if (prot as usize) & PROT_EXEC != 0 {
                match jit_arena_alloc(len) {
                    Some(p) => {
                        JIT_EXEC_MAPS.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
                        p as SyscallReturnValue
                    }
                    None => {
                        debug_println!(
                            "[render-pd] JIT arena EXHAUSTED on exec mmap({} KiB)",
                            len / 1024
                        );
                        -ENOMEM
                    }
                }
            } else {
                (unsafe {
                    MMAP_DLMALLOC.alloc(Layout::from_size_align(len.max(1), 4096).unwrap())
                }) as SyscallReturnValue
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
        other => {
            debug_println!("[render-pd] UNHANDLED SYSCALL (a precise wall): {other:?}");
            -ENOSYS
        }
    }
}

// ───────────────────────── the JIT W→X arena ────────────────────────────────
//
// A static byte arena that backs every executable mapping the LLVM JIT requests.
// It is executable because the `aarch64-sel4-roottask-musl` target links
// `--no-rosegment`, so the seL4 kernel maps the whole root-task image (this static
// included) with execute permission — the same property that lets the root task's
// own `.text` run. A bump allocator hands out page-aligned runs; the JIT writes
// code in and runs it (W and X coexist — the simplest faithful service of the W→X
// requirement, with no new seL4 capability). On overflow we report a precise wall
// (grow JIT_ARENA_SIZE), never fake success.

const JIT_ARENA_SIZE: usize = 16 * 1024 * 1024;

#[repr(align(4096))]
struct JitArena([u8; JIT_ARENA_SIZE]);

// In `.data` (not `.bss`): a zero-init `.bss` static is fine for code (the JIT
// overwrites it), but keeping it in the image's mapped, executable load region is
// what matters. `#[used]` so LTO never drops it.
#[used]
static mut JIT_ARENA: JitArena = JitArena([0u8; JIT_ARENA_SIZE]);
static JIT_ARENA_NEXT: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);

/// Observability of the W→X path (printed by the driver / a debug hook): how many
/// executable mmaps and PROT_EXEC mprotect flips the JIT performed.
static JIT_EXEC_MAPS: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);
static JIT_WX_FLIPS: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(0);

/// Bump-allocate a page-aligned run of `len` bytes from the RWX JIT arena.
fn jit_arena_alloc(len: usize) -> Option<*mut u8> {
    use core::sync::atomic::Ordering;
    let len = (len + 0xFFF) & !0xFFF; // round up to a page
    let mut cur = JIT_ARENA_NEXT.load(Ordering::Relaxed);
    loop {
        let next = cur.checked_add(len)?;
        if next > JIT_ARENA_SIZE {
            return None;
        }
        match JIT_ARENA_NEXT.compare_exchange_weak(cur, next, Ordering::AcqRel, Ordering::Relaxed)
        {
            Ok(_) => {
                let base = core::ptr::addr_of_mut!(JIT_ARENA) as *mut u8;
                return Some(unsafe { base.add(cur) });
            }
            Err(actual) => cur = actual,
        }
    }
}

/// Exposed to the C driver so it can report the W→X activity it provoked.
#[unsafe(no_mangle)]
pub extern "C" fn dregg_render_pd_jit_exec_maps() -> usize {
    JIT_EXEC_MAPS.load(core::sync::atomic::Ordering::Relaxed)
}
#[unsafe(no_mangle)]
pub extern "C" fn dregg_render_pd_jit_wx_flips() -> usize {
    JIT_WX_FLIPS.load(core::sync::atomic::Ordering::Relaxed)
}

// ───────────────────────── heap + anon mmap pools ───────────────────────────
//
// Sized larger than the executor PD: lavapipe + static LLVM has a heavier
// footprint (the JIT's data structures, the rasterizer tiles, the 800×600×4
// framebuffer). These are static PD memory (the root task's own image frames).
static BRK_HEAP: StaticHeap<{ 8 * 1024 * 1024 }> = StaticHeap::new();

const MMAP_HEAP_SIZE: usize = 256 * 1024 * 1024;
static MMAP_HEAP: StaticHeap<MMAP_HEAP_SIZE> = StaticHeap::new();
static MMAP_DLMALLOC: StaticDlmalloc<RawOneShotMutex> = StaticDlmalloc::new(MMAP_HEAP.bounds());
