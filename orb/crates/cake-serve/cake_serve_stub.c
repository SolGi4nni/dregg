/*
 * Stand-in for the verified compiler's emitted export-function serve stage.
 *
 * It reproduces the parts of the runtime ABI the host integration depends on,
 * so the Rust scaffold in src/lib.rs can be exercised end to end before the
 * real emitted object is dropped in:
 *
 *   - `serve(ctrl, req, len, resp)` : the export function. SysV ABI, so the
 *     four args arrive in rdi/rsi/rdx/rcx. No callback FFI, no garbage
 *     collector. Transforms `req` into `resp` and returns the byte count.
 *
 *   - `cml_main()` : runtime init. In the real object this reads the heap/stack
 *     region slots, hands them to the runtime, and (with main-return enabled)
 *     RETURNS instead of running the whole program to exit. Modelled here as a
 *     per-thread "runtime is ready" latch plus a heap allocation frontier.
 *
 *   - the heap/stack region slots. The real object emits these as three
 *     PROCESS-GLOBAL data words. A per-core-shard reactor wants one heap PER
 *     SHARD; the fix modelled here is to give the slots THREAD-LOCAL storage,
 *     so each shard thread gets its own region with no cross-shard aliasing.
 *     The host installs a thread's region with `cake_shard_install` before it
 *     calls `cml_main` the first time.
 *
 * The transform is deliberately routed THROUGH this thread's own heap scratch
 * (write, then read back) and guards a canary across a widened window, so that
 * two shards sharing a single heap would corrupt each other and be caught. The
 * per-shard-heap property is load-bearing here, not cosmetic.
 */
#include <stddef.h>
#include <stdint.h>

/* Runtime region slots — one instance PER THREAD (thread-local storage). This
 * is the per-shard-heap solution: the real object emits process-global words;
 * giving them thread-local storage class makes each reactor shard's heap
 * private to its own core thread. */
static __thread unsigned char *rt_heap;
static __thread unsigned char *rt_stackend;
static __thread unsigned char *rt_frontier; /* bump pointer into this thread's heap */
static __thread int rt_ready;               /* set by cml_main, checked by serve */

/* control byte the host places at ctrl[0]; salts the output so the test can
 * confirm the control-block argument actually flows through the ABI. */

/* Host installs this thread's heap/stack region before the first init. The
 * `stack` argument is accepted to mirror the real three-slot ABI; this stand-in
 * does its scratch work inside the heap span [rt_heap, rt_stackend). */
void cake_shard_install(unsigned char *heap, unsigned char *stack, unsigned char *stackend) {
    (void)stack;
    rt_heap = heap;
    rt_stackend = stackend;
    rt_ready = 0;
}

/* Runtime init. Sets this thread's heap frontier and latches "ready". Returns
 * (main-return model) instead of running to program exit. */
void cml_main(void) {
    rt_frontier = rt_heap;
    rt_ready = 1;
}

/* The exported serve function. SysV ABI: rdi=ctrl, rsi=req, rdx=len, rcx=resp.
 * Returns the number of bytes written into `resp`, or a negative code on a
 * broken precondition. */
long serve(unsigned char *ctrl, unsigned char *req, long len, unsigned char *resp) {
    if (!rt_ready) {
        return -1; /* init-once-per-thread contract violated */
    }
    if (len < 0) {
        return -3;
    }
    /* Bump-allocate scratch from this thread's own heap; refuse if it would run
     * past the region end. */
    unsigned char *scratch = rt_frontier;
    if (scratch + (size_t)len + 8 > rt_stackend) {
        return -4; /* heap exhausted */
    }

    /* Stage 1: transform request into per-thread heap scratch. */
    for (long i = 0; i < len; i++) {
        unsigned char k = (unsigned char)(0xA5u ^ (unsigned)i);
        scratch[i] = (unsigned char)(req[i] ^ k);
    }

    /* Canary just past the scratch, in this thread's own heap. A second shard
     * that shared this heap could clobber it during the window below. */
    uint64_t canary = 0x0123456789ABCDEFull ^ (uint64_t)(uintptr_t)req;
    uint64_t *guard = (uint64_t *)(scratch + len);
    *guard = canary;
    for (volatile int s = 0; s < 512; s++) {
        /* widen any cross-shard race window */
    }
    if (*guard != canary) {
        return -2; /* heap was shared across shards: corruption detected */
    }

    /* Stage 2: read back from per-thread scratch into the caller's borrowed
     * response buffer (zero-copy: `resp` is the caller's memory). */
    unsigned char salt = ctrl ? ctrl[0] : 0;
    for (long i = 0; i < len; i++) {
        resp[i] = (unsigned char)(scratch[i] ^ salt);
    }
    return len;
}
