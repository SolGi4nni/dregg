/* Re-entrant host driver for the certified export-function serve (serve.S),
 * with PER-SHARD IMAGES so many reactor shards serve in parallel.
 *
 * Each emitted image is compiled with main-return enabled: its cml_main()
 * initialises the runtime from that image's region slots (cakeI_cml_heap /
 * cakeI_cml_stack / cakeI_cml_stackend) and RETURNS to the host, rather than
 * running to program exit. After that one-time init, the image's export function
 *
 *     uint64_t cakeI_serve(uint64_t ctrl, uint64_t req, uint64_t len, uint64_t out)
 *
 * is an ordinary SysV-ABI symbol callable repeatedly. serve returns the number
 * of response bytes written into out.
 *
 * ## Per-shard heaps (the parallel-safe fix)
 *
 * A single image keeps its heap frontier and saved runtime state (ret_base /
 * ret_stack / ret_stackend / can_enter) in fixed-address words its machine code
 * reaches rip-relative. Two threads driving the same image would race those
 * words and corrupt each other's heap. Those words cannot be made thread-local
 * without re-emitting the code, so build-cake-lib.sh instead mints N
 * symbol-disjoint COPIES of the object (cake_images_gen.h wires their entry
 * points and region slots into the tables below). Each shard thread claims one
 * image index and drives ONLY that image, so image i's heap/stack/state is
 * touched by exactly one thread — N shards serve concurrently with no shared
 * mutable runtime state and no lock.
 *
 * The host binds an image to a thread by calling cake_serve_http_shard(idx, ...)
 * with a per-thread `idx` in [0, cake_image_count()). Indices past the image
 * count are declined (return 0) and the caller falls through to the leanc serve.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* The N per-shard images: extern decls for each image's serve/cml_main/region
 * slots, plus the CAKE_IMAGE_COUNT and the dispatch tables (cake_heap_slot,
 * cake_stack_slot, cake_stackend_slot, cake_init_fn, cake_serve_fn). */
#include "cake_images_gen.h"

/* Runtime hooks every image references but does not define (left un-prefixed by
 * the image mint, so all images share one definition). On a normal serve
 * neither fires; cml_err reports a broken runtime precondition. */
void cml_clear(void) { }
void cml_err(int arg) { fprintf(stderr, "cake serve: runtime error %d\n", arg); }
void cml_exit(int arg) { (void)arg; }

/* PROVENANCE COUNTER: incremented once per serve that returns a nonzero length.
 * Read/written from multiple shard threads now, so bump it atomically. A nonzero
 * value after a request proves the emitted machine code ran to a response. */
uint64_t cake_serve_report_count = 0;

/* Per-image region + init latch. Entry i is owned by whichever single shard
 * thread claimed image index i, so no locking is needed on these. */
static void *g_region[CAKE_IMAGE_COUNT];
static int   g_ready[CAKE_IMAGE_COUNT];
static const unsigned long HEAP_SZ  = 64UL * 1024 * 1024;
static const unsigned long STACK_SZ = 16UL * 1024 * 1024;

/* Number of parallel per-shard images the linked object provides. */
int cake_image_count(void) { return CAKE_IMAGE_COUNT; }

/* Idempotent one-time init of image `idx` on its owning thread: allocate the
 * image's region, point its slots at it, and run its cml_main once (it returns
 * under main-return). Returns 0 on success, nonzero on a bad index or OOM. */
int cake_serve_init_shard(int idx) {
    if (idx < 0 || idx >= CAKE_IMAGE_COUNT) return 1;
    if (g_ready[idx]) return 0;
    void *r = malloc(HEAP_SZ + STACK_SZ);
    if (!r) return 1;
    *cake_heap_slot[idx]     = r;
    *cake_stack_slot[idx]    = (char *)r + HEAP_SZ;
    *cake_stackend_slot[idx] = (char *)r + HEAP_SZ + STACK_SZ;
    cake_init_fn[idx]();
    g_region[idx] = r;
    g_ready[idx] = 1;
    return 0;
}

/* Stage the control block for the served route, exactly as the validated
 * standalone harness stages it: the IP-filter address bytes, the HSTS max-age,
 * the redirect status code, the response-body source, and the two header
 * templates the response threads. These are the route's fixed serve
 * configuration; the request line itself (method/target/version) is parsed by
 * the emitted code out of req. */
static void stage_ctrl(unsigned char *ctrl) {
    static const unsigned char addr[] = { 1, 2, 3 };
    uint64_t AL = (uint64_t)sizeof(addr);
    memcpy(ctrl + 8192, addr, sizeof(addr));       /* abuf  -> ctrl+8192 */
    memcpy(ctrl + 8,  &AL, 8);                      /* count -> ctrl+8    */

    uint64_t maxage = 31536000;                    /* HSTS max-age       */
    uint64_t code   = 200;                          /* status seed        */
    memcpy(ctrl + 16, &maxage, 8);
    memcpy(ctrl + 24, &code,   8);

    unsigned char *src = ctrl + 16384;              /* body source (159B) */
    for (int i = 0; i < 159; i++) src[i] = (unsigned char)(0x20 + (i % 90));

    const char *hs = "Strict-Transport-Security: max-age=31536000\r\n";
    uint64_t HL = (uint64_t)strlen(hs);
    memcpy(ctrl + 16640, hs, HL);
    const char *ls = "Location: /\r\n";
    uint64_t LOCL = (uint64_t)strlen(ls);
    memcpy(ctrl + 16896, ls, LOCL);
    memcpy(ctrl + 112, &HL,   8);                  /* hsts tmpl len -> ctrl+112 */
    memcpy(ctrl + 120, &LOCL, 8);                  /* loc  tmpl len -> ctrl+120 */
}

/* Serve one request through per-shard image `idx`, in-process. Stages the
 * control block, calls that image's export function once, and copies the
 * response into out (capped at cap). Returns the number of response bytes, or 0
 * on a bad/unavailable image or a broken precondition (the caller then falls
 * through to the deployed path). The control/request scratch is allocated and
 * freed here, so req/out never alias the runtime's staging memory.
 *
 * Thread-safety: distinct `idx` values touch disjoint image state, so different
 * shard threads may run this concurrently with no lock. Two threads must never
 * pass the SAME idx concurrently — the host assigns one idx per thread. */
size_t cake_serve_http_shard(int idx, const uint8_t *req, size_t req_len,
                             uint8_t *out, size_t out_cap) {
    if (idx < 0 || idx >= CAKE_IMAGE_COUNT) return 0;
    if (!g_ready[idx]) { if (cake_serve_init_shard(idx)) return 0; }

    unsigned char *ctrl = calloc(1, 32768);
    unsigned char *rbuf = calloc(1, 4096);
    unsigned char *obuf = calloc(1, 4096);
    if (!ctrl || !rbuf || !obuf) { free(ctrl); free(rbuf); free(obuf); return 0; }

    /* The pipeline parses a single request LINE (method SP target SP version).
     * Take the wire bytes up to the first CRLF so a full request with headers
     * serves off its start-line; the trailing header block is not consumed. */
    uint64_t L = req_len > 4096 ? 4096 : (uint64_t)req_len;
    for (uint64_t i = 0; i + 1 < L; i++) {
        if (req[i] == '\r' && req[i + 1] == '\n') { L = i; break; }
    }
    if (req && L) memcpy(rbuf, req, (size_t)L);
    stage_ctrl(ctrl);

    uint64_t total = cake_serve_fn[idx]((uint64_t)ctrl, (uint64_t)rbuf, L, (uint64_t)obuf);

    size_t n = 0;
    if ((int64_t)total > 0) {
        n = (size_t)total;
        if (n > out_cap) n = out_cap;
        if (out && n) memcpy(out, obuf, n);
        __atomic_add_fetch(&cake_serve_report_count, 1, __ATOMIC_RELAXED);
    }
    free(ctrl); free(rbuf); free(obuf);
    return n;
}

/* Back-compat single-owner entry: drive image 0. Kept so any caller that has
 * not adopted the sharded entry still works (image 0 on the calling thread). */
int cake_serve_init(void) { return cake_serve_init_shard(0); }

size_t cake_serve_http(const uint8_t *req, size_t req_len,
                       uint8_t *out, size_t out_cap) {
    return cake_serve_http_shard(0, req, req_len, out, out_cap);
}
