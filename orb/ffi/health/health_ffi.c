/* Re-entrant FFI driver + host wrapper for health.S (cake --pancake output).
 *
 * The arena probes (collect/boundscan/...) ran the CakeML-compiled program as a
 * ONE-SHOT process: main() set up the heap and called cml_main() exactly once,
 * cake_main ran to completion and called cml_exit -> exit(). That shape is not
 * callable from a long-lived server thread.
 *
 * This driver makes cake_main callable REPEATEDLY in-process:
 *   - health_serve() stashes (req, out) in statics, resets the CakeML heap/stack
 *     layout, and invokes cml_main() behind a setjmp;
 *   - cml_exit/cml_err (which cake_main tail-calls on completion) are overridden
 *     to longjmp back into health_serve instead of exit()ing the whole process.
 * CakeML re-initialises its heap from cml_heap/cml_stack/cml_stackend on every
 * cml_main entry, and its runtime stack lives in the malloc'd region (not the C
 * stack that longjmp unwinds), so each call is a clean re-run.
 *
 * The FFI contract of health.pnk:
 *   @load_vec(ctrl, 24, reqbuf, 4096)  -> ffiload_vec:  reqbuf := stashed request,
 *                                         ctrl[0..8)   := request length.
 *   @report_vec(outbuf, 4096, ctrl, 24)-> ffireport_vec: read count from ctrl[8..16),
 *                                         stashed_out[0..count) := outbuf[0..count).
 *
 * No dependency on the stock basis_ffi.c: this file provides every external
 * symbol health.S references (the two FFIs + cml_exit/cml_err/cml_clear + the
 * empty GC ffi), so it links cleanly into a library with no main().
 */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <setjmp.h>

/* exported by health.S (cake --pancake output) */
extern void cml_main(void);
extern void *cml_heap;
extern void *cml_stack;
extern void *cml_stackend;

static void *g_heap_base = 0;
static unsigned long g_heap_sz = 0;
static unsigned long g_stack_sz = 0;

static const uint8_t *g_req = 0;
static size_t g_req_len = 0;
static uint8_t *g_out = 0;
static size_t g_out_cap = 0;
static size_t g_out_len = 0;

/* PROVENANCE COUNTER: incremented ONLY inside ffireport_vec, i.e. only when the
 * CakeML-compiled code has run to completion and reported its response bytes on
 * the FFI trace. A nonzero value after a request proves the compiled machine
 * code executed on that request. */
uint64_t cake_health_report_count = 0;

static jmp_buf g_exit_jmp;

/* @load_vec: source the stashed request into reqbuf; length into ctrl[0..8). */
void ffiload_vec(unsigned char *c, long clen, unsigned char *a, long alen) {
    (void)clen;
    uint64_t len = (uint64_t)g_req_len;
    if ((long)len > alen) len = (uint64_t)alen;
    if (g_req && len) memcpy(a, g_req, (size_t)len);
    memcpy(c, &len, 8);
}

/* @report_vec: sink outbuf[0..count) (count from ctrl[8..16)) into stashed out. */
void ffireport_vec(unsigned char *c, long clen, unsigned char *a, long alen) {
    (void)clen; (void)alen;
    uint64_t count = 0;
    memcpy(&count, a + 8, 8);
    if (count > (uint64_t)g_out_cap) count = (uint64_t)g_out_cap;
    if (g_out && count) memcpy(g_out, c, (size_t)count);
    g_out_len = (size_t)count;
    cake_health_report_count += 1;
}

/* Re-entrancy hooks: cake_main tail-calls cml_exit/cml_err on completion; bounce
 * back into health_serve instead of tearing down the process. */
void cml_exit(int arg) { longjmp(g_exit_jmp, arg + 1); }
void cml_err(int arg)  { longjmp(g_exit_jmp, arg + 1); }
void cml_clear(void)   { }

/* The empty tracing/GC FFI CakeML may reference (no-op in non-DEBUG builds). */
void ffi(unsigned char *c, long clen, unsigned char *a, long alen) {
    (void)c; (void)clen; (void)a; (void)alen;
}

/* Run the cake-compiled /health responder once, in-process. Returns the number
 * of response bytes written into `out` (379 for the exact template request; 0
 * for anything else, so the caller falls through to the leanc path). */
size_t health_serve(const uint8_t *req, size_t req_len,
                     uint8_t *out, size_t out_cap) {
    if (!g_heap_base) {
        g_heap_sz  = 16UL * 1024 * 1024;
        g_stack_sz = 16UL * 1024 * 1024;
        g_heap_base = malloc(g_heap_sz + g_stack_sz);
        if (!g_heap_base) return 0;
    }
    g_req = req; g_req_len = req_len;
    g_out = out; g_out_cap = out_cap; g_out_len = 0;

    cml_heap = g_heap_base;
    cml_stack = (char *)g_heap_base + g_heap_sz;
    cml_stackend = (char *)cml_stack + g_stack_sz;

    if (setjmp(g_exit_jmp) == 0) {
        cml_main();
    }
    return g_out_len;
}
