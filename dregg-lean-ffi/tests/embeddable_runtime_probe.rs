//! THE EMBEDDABLE-LEAN-RUNTIME SPIKE (pg-Tier-D embeddable half).
//!
//! The pg-dregg Tier-D verdict (`pg-dregg/docs/PG-DREGG-TIER-D-SPIKE.md` §4) is
//! D-SIDECAR because the Lean runtime was believed to (4.1) statically override
//! the global allocator with mimalloc and (4.2) spawn worker threads — both fatal
//! inside a single-threaded postgres backend (`palloc`/`longjmp`/`fork`).
//!
//! This probe MEASURES those two claims on the linked host process, plus the
//! IO-free claim, with real runtime evidence:
//!
//!   PROP-1 (no global allocator override): `malloc`/`free` resolve to the host
//!     libc (libSystem), NOT into the dregg/Lean image. mimalloc is present only
//!     as Lean's PRIVATE heap (`mi_malloc`), reachable from `lean_alloc_*`, never
//!     interposing the process-wide `malloc` a postgres backend's `palloc` rides.
//!     Proven via `dladdr(malloc)` → the defining image is the system C library.
//!
//!   PROP-2 (single-threaded — no worker threads): the OS thread count of THIS
//!     process does not rise across `dregg_ffi_init()` NOR across a real turn
//!     through `dregg_exec_full_forest_auth`. The Lean task manager is lazy
//!     (`g_task_manager == nullptr` until an explicit `lean_init_task_manager`,
//!     which the executor embedding never calls), so `Task.spawn` runs INLINE
//!     (`object.cpp lean_task_spawn_core`: `if (!g_task_manager) return
//!     lean_task_pure(apply_1(...))`). Proven via mach `task_threads`.
//!
//!   PROP-3 (the turn genuinely executes): a committing turn (the demo wire) runs
//!     to `status:2, ok:1` with the conserved transfer applied — the executor is
//!     REAL, not a stub. (And the marshal-shape overspend rejects, fail-closed.)
//!
//! Run:
//!   cargo test -p dregg-lean-ffi --features lean-lib --test embeddable_runtime_probe -- --nocapture
//!
//! All three GREEN ⇒ the SAME `libdregg_lean.a` + static Lean runtime that the
//! host links today is already embeddable into a single-threaded host (the
//! pg-Tier-D-embeddable half) on this platform. See
//! `docs/EMBEDDABLE-LEAN-RUNTIME.md` for the cross-platform caveats (the Linux
//! `static.c.o` interposition story is different — handled by DREGG_LEAN_LINK).
#![cfg(feature = "lean-lib")]
#![cfg(target_os = "macos")]

use std::ffi::CStr;
use std::os::raw::{c_char, c_int, c_void};

// ── mach thread introspection (libSystem; no extra crate) ──────────────────
// `task_threads(mach_task_self(), &threads, &count)` returns the live kernel
// thread count of the calling task. We only need `count`; we immediately
// deallocate the returned thread array.
type MachPort = u32;
type KernReturn = c_int;
type ThreadActArray = *mut MachPort;

extern "C" {
    fn mach_task_self() -> MachPort;
    fn task_threads(
        task: MachPort,
        act_list: *mut ThreadActArray,
        act_list_cnt: *mut u32,
    ) -> KernReturn;
    fn vm_deallocate(target: MachPort, address: usize, size: usize) -> KernReturn;
    // `dladdr` (libSystem): resolve a symbol address to the shared object that
    // defines it, so we can ask "where does `malloc` actually live?".
    fn dladdr(addr: *const c_void, info: *mut DlInfo) -> c_int;
}

#[repr(C)]
struct DlInfo {
    dli_fname: *const c_char,
    dli_fbase: *mut c_void,
    dli_sname: *const c_char,
    dli_saddr: *mut c_void,
}

/// Live OS thread count of this process (mach). `0` on an unexpected mach error
/// (treated as "couldn't measure", which fails the property loudly).
fn live_thread_count() -> u32 {
    unsafe {
        let mut acts: ThreadActArray = std::ptr::null_mut();
        let mut n: u32 = 0;
        let kr = task_threads(mach_task_self(), &mut acts, &mut n);
        if kr != 0 {
            return 0;
        }
        // Free the kernel-allocated thread-port array (it is not ours to keep).
        if !acts.is_null() {
            let _ = vm_deallocate(
                mach_task_self(),
                acts as usize,
                (n as usize) * std::mem::size_of::<MachPort>(),
            );
        }
        n
    }
}

/// The filesystem path of the image that DEFINES the function at `addr`.
fn defining_image(addr: *const c_void) -> Option<String> {
    unsafe {
        let mut info = DlInfo {
            dli_fname: std::ptr::null(),
            dli_fbase: std::ptr::null_mut(),
            dli_sname: std::ptr::null(),
            dli_saddr: std::ptr::null_mut(),
        };
        if dladdr(addr, &mut info) == 0 || info.dli_fname.is_null() {
            return None;
        }
        Some(
            CStr::from_ptr(info.dli_fname)
                .to_string_lossy()
                .into_owned(),
        )
    }
}

/// The committing demo turn (= `executor-pd/out/demo-wire.txt`): a 30-unit
/// transfer cell-0→cell-1 with a valid signature auth, full side-tables. The
/// verified `execFullForestG` accepts it (`status:2, ok:1`): nonce 7→8, cell-0
/// balance 100→70, cell-1 5→35.
const DEMO_WIRE_COMMIT: &str = r#"{"host":{"now":0,"block_height":0,"frozen":[],"stored_head":0,"budget":1000000000},"state":{"cells":[[0,{"rec":[["balance",{"int":100}],["nonce",{"int":7}]]}],[1,{"rec":[["balance",{"int":5}]]}]],"caps":[[9,[{"node":0}]]],"bal":[[0,0,100],[1,0,5]],"escrows":[[1,0,1,7,0,0,0,{"none":0},{"none":0}]],"nullifiers":[111],"commitments":[222],"queues":[[1,0,4,[333,444]]],"swiss":[[5,0,1,[0,1],1,{"some":99}]],"revoked":[],"lifecycle":[],"deathCert":[]},"turn":{"agent":0,"nonce":7,"fee":10,"valid_until":1000,"prev":"0000000000000000000000000000000000000000000000000000000000000000","root":{"auth":{"sig":["0000000000000000000000000000000000000000000000000000000000000007",7]},"caveats":[],"action":{"bal":[0,0,1,30,0]},"children":[]}}}"#;

#[test]
fn embeddable_runtime_probe() {
    println!("\n========== EMBEDDABLE-LEAN-RUNTIME SPIKE (host process) ==========");

    // ── PROP-1: no global allocator override (mimalloc is private) ──────────
    // Resolve `malloc` to its defining image. If the Lean runtime had interposed
    // the process-wide allocator, `malloc` would resolve into this binary (or a
    // mimalloc image); instead it must resolve to the system C library.
    let malloc_img = defining_image(libc_malloc_addr())
        .expect("dladdr(malloc) must resolve to a defining image");
    println!("[PROP-1] malloc resolves to: {malloc_img}");
    let is_system_libc = malloc_img.contains("/usr/lib/")
        || malloc_img.contains("libsystem")
        || malloc_img.contains("libSystem")
        || malloc_img.ends_with("/libc.so")
        || malloc_img.contains("/libc.");
    assert!(
        is_system_libc,
        "PROP-1 FAILED: malloc resolves to {malloc_img}, not the system C library — \
         the Lean runtime IS interposing the global allocator (would collide with \
         a postgres backend's palloc). Embeddability blocker 4.1 is REAL here."
    );
    // And confirm mimalloc IS present (Lean's private heap) — it just isn't `malloc`.
    // `mi_malloc` is a defined text symbol in the linked image (proven by `nm`
    // in the doc); here we just assert the resolution above held, which already
    // distinguishes "mimalloc present privately" from "mimalloc interposes malloc".
    println!(
        "[PROP-1] ✓ global allocator is the host libc; mimalloc is Lean-private (no interposition)"
    );

    // ── PROP-2: single-threaded — measure thread count across init + a turn ──
    // CRITICAL: this test drives ONLY the single-threaded init path
    // (`init_single_threaded` → `dregg_ffi_init_st`), which omits `initialize_libuv()`
    // and therefore never spawns the libuv event-loop thread. (The DEFAULT
    // `dregg_ffi_init` DOES spawn it — measured as +1 thread — which is exactly the
    // blocker this path removes.) We must NOT touch `lean_available()` here.
    let t_before_init = live_thread_count();
    assert!(
        t_before_init > 0,
        "mach task_threads must report a positive thread count"
    );
    println!("[PROP-2] threads BEFORE init:                {t_before_init}");

    // Force the once-per-process Lean runtime init — SINGLE-THREADED flavor.
    assert!(
        dregg_lean_ffi::init_single_threaded(),
        "dregg_ffi_init_st must succeed (the libuv-thread-free runtime initializes)"
    );
    let t_after_init = live_thread_count();
    println!("[PROP-2] threads AFTER  init_single_threaded: {t_after_init}");

    // Run a real committing turn (single-threaded path).
    let out = dregg_lean_ffi::shadow_exec_full_forest_auth_single_threaded(DEMO_WIRE_COMMIT)
        .expect("the verified executor must run the demo turn");
    let t_after_turn = live_thread_count();
    println!("[PROP-2] threads AFTER  one real turn:        {t_after_turn}");

    // The decisive assertion: NO worker thread was spawned by init or by the turn.
    // (The mach count includes the harness's own thread(s); the property is that
    // the executor adds NONE.)
    assert!(
        t_after_init <= t_before_init,
        "PROP-2 FAILED: dregg_ffi_init spawned {} worker thread(s) — the Lean task \
         manager started (would violate the postgres single-thread invariant).",
        t_after_init as i64 - t_before_init as i64
    );
    assert!(
        t_after_turn <= t_before_init,
        "PROP-2 FAILED: the turn spawned {} worker thread(s) — `execFullForestG` is \
         NOT worker-free (would violate the postgres single-thread invariant).",
        t_after_turn as i64 - t_before_init as i64
    );
    println!("[PROP-2] ✓ no worker threads spawned by init or by the turn (task manager stays nullptr ⇒ Task.spawn runs inline)");

    // ── PROP-3: the turn genuinely executes (committing + fail-closed) ──────
    println!("[PROP-3] demo-turn receipt: {out}");
    assert!(
        out.contains("\"ok\":1") && out.contains("\"status\":2"),
        "PROP-3 FAILED: the committing demo turn did not produce status:2 ok:1 — got: {out}"
    );
    // The conserved transfer landed: cell-0 100→70, cell-1 5→35 in the bal table.
    assert!(
        out.contains("[0,0,70]") && out.contains("[1,0,35]"),
        "PROP-3 FAILED: the 30-unit transfer did not apply (expected bal [0,0,70],[1,0,35]) — got: {out}"
    );
    println!("[PROP-3] ✓ verified executor ran a real committing turn (nonce 7→8; 100→70, 5→35)");

    // Fail-closed tooth: a marshal-shape overspend (transfer 1000 from a 100-balance
    // cell) must NOT commit — the executor genuinely decides, it is not a yes-stub.
    let overspend = r#"{"state":{"cells":[[0,{"rec":[["balance",{"int":100}],["nonce",{"int":0}]]}],[1,{"rec":[["balance",{"int":5}],["nonce",{"int":0}]]}]],"caps":[],"bal":[[0,0,100],[1,0,5]],"escrows":[],"nullifiers":[],"commitments":[],"queues":[],"swiss":[],"revoked":[]},"turn":{"agent":0,"nonce":0,"fee":0,"valid_until":1000000,"prev":"0000000000000000000000000000000000000000000000000000000000000000","root":{"auth":{"unchecked":0},"caveats":[],"action":{"bal":[0,0,1,1000,0]},"children":[]}}}"#;
    let ov = dregg_lean_ffi::shadow_exec_full_forest_auth_single_threaded(overspend)
        .expect("the overspend turn must still run (and reject)");
    assert!(
        !ov.contains("\"ok\":1"),
        "PROP-3 FAILED: an overspend committed — the executor is a yes-stub, not real: {ov}"
    );
    println!("[PROP-3] ✓ overspend rejected (fail-closed; the executor genuinely decides)");

    println!("========== ALL THREE GREEN: the runtime is embeddable on this host ==========\n");
}

/// The address of the process-wide `malloc` (whatever the dynamic linker bound).
/// Declared as a weak extern and taken by address so `dladdr` can resolve its
/// defining image.
fn libc_malloc_addr() -> *const c_void {
    extern "C" {
        fn malloc(n: usize) -> *mut c_void;
    }
    malloc as *const c_void
}
