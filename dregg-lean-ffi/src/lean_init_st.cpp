/* lean_init_st.cpp — the SINGLE-THREADED, IO-thread-free Lean runtime init.
 *
 * THE EMBEDDABLE-LEAN-RUNTIME path (docs/EMBEDDABLE-LEAN-RUNTIME.md). The default
 * `dregg_ffi_init` (lean_init.c) calls `lean_initialize_runtime_module()`, which
 * runs the full init chain INCLUDING `initialize_libuv()`. On a multi-thread Lean
 * build that call spawns the **libuv event-loop thread** (libuv.cpp:
 * `lthread([]{ event_loop_run_loop(&global_ev); })`) — measured as a +1 OS thread
 * at init. A postgres backend is strictly single-threaded
 * (`pg-dregg/docs/PG-DREGG-TIER-D-SPIKE.md` §4.2), so that background thread is a
 * blocker for hosting the executor IN the backend.
 *
 * The fix is the HOST analogue of the seL4 executor-PD's libuv excision
 * (`sel4/dregg-pd/executor-pd/scripts/build-leanrt-elf.sh`, which patches
 * `init_module.cpp` to drop `initialize_libuv()`): here we simply DO NOT call
 * `lean_initialize_runtime_module()` at all. Instead we call the eight individual
 * `lean::initialize_*` initializers directly (each is an exported, linkable symbol
 * in its own `libleanrt.a` member), in the SAME order `init_module.cpp` uses, but
 * OMITTING `initialize_libuv()`. Because we never reference
 * `lean_initialize_runtime_module`, the linker never pulls `init_module.cpp.o`,
 * which is the only thing that references `initialize_libuv` / `libuv.cpp.o` — so
 * the event-loop thread is never even linked in.
 *
 * SOUNDNESS: the pure executor turn (`dregg_exec_full_forest_auth` =
 * `execFullForestG` + admission) performs NO socket/file/timer IO (it is a
 * deterministic fold over the wire). It needs the IO-MONAD CORE (`initialize_io`,
 * which is libuv-free — heartbeats, the mono clock, `lean_io_mark_end_initialization`)
 * but NONE of the libuv event loop. The verified closure references no libuv symbol
 * (confirmed by `nm`), and the executor never calls `lean_init_task_manager`, so the
 * task manager stays `nullptr` and `Task.spawn` runs inline (object.cpp:
 * `lean_task_spawn_core`: `if (!g_task_manager) return lean_task_pure(apply_1(...))`).
 * The result is a runtime that, in this process, spawns ZERO threads of its own.
 *
 * This file is compiled by build.rs (alongside lean_init.c) ONLY when the linked
 * archive is present; it is purely ADDITIVE — the default `dregg_ffi_init` path is
 * untouched, so no existing consumer (node / dregg-turn shadow tests) changes.
 */
#include <lean/lean.h>

/* SHARED-vs-STATIC linkage (DREGG_LEAN_SHARED, set by build.rs in
 * `DREGG_LEAN_LINK=shared` mode — the cdylib path, e.g. the pgrx extension):
 *
 *   * STATIC (the host probe + the standalone node): `libleanrt.a` is linked, so the
 *     eight individual `lean::initialize_*` C++ symbols are available. We call them
 *     directly and OMIT `initialize_libuv` → the libuv event-loop thread is never even
 *     linked (the true libuv-thread-free init, measured 2→2→2 by the embeddable probe).
 *
 *   * SHARED (the cdylib): `libleanshared` HIDES the individual `lean::initialize_*`
 *     symbols (and the runtime internals they use — mpz/utf8/heartbeat/…), exporting
 *     only the C-ABI `lean_initialize_runtime_module`. Supplying the hidden internals
 *     from a static `libleanrt.a` copy creates a SPLIT-BRAIN runtime (two copies of the
 *     runtime's global state) that SIGSEGVs in-process. So under shared linkage the ST
 *     init MUST route through the single exported `lean_initialize_runtime_module`
 *     (ONE runtime copy) — which DOES start the libuv thread. The shared-mode
 *     `dregg_ffi_init_st` is therefore single-RUNTIME but NOT libuv-thread-free; the
 *     libuv-free property is a STATIC-link property (docs/EMBEDDABLE-LEAN-RUNTIME.md §5).
 */
#ifndef DREGG_LEAN_SHARED
namespace lean {
/* The eight libuv-free initializers from init_module.cpp's chain (each defined in
 * its own runtime object: alloc/debug/object/io/thread/mutex/process/stack_overflow).
 * `initialize_libuv` is deliberately NOT declared or called. */
void initialize_alloc();
void initialize_debug();
void initialize_object();
void initialize_io();
void initialize_thread();
void initialize_mutex();
void initialize_process();
void initialize_stack_overflow();
}
#else
extern "C" {
/* The exported C-ABI full runtime init (libleanshared exports this; it runs the whole
 * init chain INCLUDING initialize_libuv). Used ONLY in shared mode — see the header. */
void lean_initialize_runtime_module(void);
}
#endif

/* The module initializers we must run (mirrors lean_init.c's dregg_ffi_init). The
 * executor FFI module plus the four out-of-closure gate modules; each is `extern "C"`
 * with C linkage (Lean's `@[export]` / `initialize_*` symbols are C-ABI). */
extern "C" {
lean_object *initialize_Dregg2_Dregg2_Exec_FFI(uint8_t builtin);
#ifdef DREGG_FINALIZE_GATE
lean_object *initialize_Dregg2_Dregg2_Distributed_FinalityGate(uint8_t builtin);
#endif
#ifdef DREGG_STRAND_ADMIT
lean_object *initialize_Dregg2_Dregg2_Distributed_StrandAdmission(uint8_t builtin);
#endif
#ifdef DREGG_DISTRIBUTED_EXPORTS
lean_object *initialize_Dregg2_Dregg2_Exec_DistributedExports(uint8_t builtin);
#endif
}

/* dregg_ffi_init_st — the single-threaded init for the executor-in-a-constrained-host
 * path. STATIC linkage: libuv-thread-free (the eight initializers, no libuv). SHARED
 * linkage (the cdylib): single-runtime via the exported `lean_initialize_runtime_module`
 * (which starts the libuv thread — see the header note + docs/EMBEDDABLE-LEAN-RUNTIME.md §5).
 *
 * Returns 0 on success, 1 if a module initializer reported an IO error. Idempotency is
 * the CALLER's responsibility (the Rust side guards it behind a OnceLock), exactly as
 * for `dregg_ffi_init`. */
extern "C" int dregg_ffi_init_st(void) {
#ifndef DREGG_LEAN_SHARED
    /* STATIC: the libuv-free prefix of lean_initialize_runtime_module(), in order. */
    lean::initialize_alloc();
    lean::initialize_debug();
    lean::initialize_object();
    lean::initialize_io();      /* IO-MONAD CORE — libuv-free; the executor needs it */
    lean::initialize_thread();  /* thread-local reset fns only; spawns nothing */
    lean::initialize_mutex();
    lean::initialize_process();
    lean::initialize_stack_overflow();
    /* initialize_libuv() — DELIBERATELY OMITTED (the event-loop thread). */
#else
    /* SHARED: the single exported runtime init (one runtime copy; starts libuv). */
    lean_initialize_runtime_module();
#endif

    lean_object *res = initialize_Dregg2_Dregg2_Exec_FFI(1);
    if (!lean_io_result_is_ok(res)) {
        lean_io_result_show_error(res);
        lean_dec_ref(res);
        return 1;
    }
    lean_dec_ref(res);
#ifdef DREGG_FINALIZE_GATE
    {
        lean_object *gres = initialize_Dregg2_Dregg2_Distributed_FinalityGate(1);
        if (!lean_io_result_is_ok(gres)) { lean_io_result_show_error(gres); lean_dec_ref(gres); return 1; }
        lean_dec_ref(gres);
    }
#endif
#ifdef DREGG_STRAND_ADMIT
    {
        lean_object *ares = initialize_Dregg2_Dregg2_Distributed_StrandAdmission(1);
        if (!lean_io_result_is_ok(ares)) { lean_io_result_show_error(ares); lean_dec_ref(ares); return 1; }
        lean_dec_ref(ares);
    }
#endif
#ifdef DREGG_DISTRIBUTED_EXPORTS
    {
        lean_object *dres = initialize_Dregg2_Dregg2_Exec_DistributedExports(1);
        if (!lean_io_result_is_ok(dres)) { lean_io_result_show_error(dres); lean_dec_ref(dres); return 1; }
        lean_dec_ref(dres);
    }
#endif
    lean_io_mark_end_initialization();
    return 0;
}
