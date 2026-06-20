// musl-compat.c — the handful of libc symbols the lean seL4/musllibc fork
// (`aarch64_sel4` ARCH) lacks but Mesa + LLVM reference at link time. Each is a
// faithful, minimal definition; none changes the render path's behaviour.
//
// Provided here (not patched into the musl) so the render-PD link is reproducible
// against the stock seL4 musl substrate executor-rootserver provisions.
//
//   * secure_getenv     — a GNU extension Mesa's env helpers reach for. With no
//                         setuid/setgid in a single seL4 PD, it is exactly getenv.
//   * qsort_r           — the reentrant qsort variant (NIR/util sort). The seL4
//                         musl ships qsort but not qsort_r; implement it on top
//                         of qsort via a thread-local trampoline (single-threaded
//                         PD ⇒ a plain static is safe).
//   * c23_timespec_get  — the C23-named timespec_get the newer libstdc++/Mesa
//                         reference; forward to the deterministic clock (the PD's
//                         clock_gettime is zeroed — time is not load-bearing for
//                         the offscreen render).
//   * __syscall_cp_asm / __cp_begin / __cp_end / __cp_cancel — musl's pthread
//                         cancellation-point machinery. The `aarch64_sel4` ARCH
//                         omits the defining asm, yet `pthread_cancel.o` (pulled
//                         transitively) references them. With LP_NUM_THREADS=0
//                         lavapipe spawns NO threads and cancels nothing, so the
//                         cancellation path is dead: __syscall_cp_asm forwards to
//                         the plain syscall, and the __cp_* markers are no-ops.

#include <stddef.h>

// ── getenv (THE single-thread lever) ─────────────────────────────────────────
// This minimal seL4 root task has a NULL `__environ`, so the libc getenv returns
// NULL for everything and `std::env::set_var` faults touching `environ` before
// main. We define getenv HERE (whole-archived ⇒ chosen over the libc's
// `getenv.o`, which lld then never pulls): a tiny in-image env table. It pins
// LP_NUM_THREADS=0 (single-threaded llvmpipe: no thrd_create, no rasterizer pool
// — the fix for `vkCreateDevice = VK_ERROR_UNKNOWN` on this single-core PD) and
// the software-driver selectors. Any other key → NULL (unset), the headless
// default. No `environ` is touched.
static int str_eq(const char *a, const char *b) {
    while (*a && *a == *b) { a++; b++; }
    return *a == *b;
}
char *getenv(const char *name) {
    if (!name) return NULL;
    static char zero[]      = "0";
    static char llvmpipe[]  = "llvmpipe";
    static char one[]       = "1";
    if (str_eq(name, "LP_NUM_THREADS"))       return zero;
    if (str_eq(name, "GALLIUM_DRIVER"))       return llvmpipe;
    if (str_eq(name, "LIBGL_ALWAYS_SOFTWARE")) return one;
    return NULL;
}

// ── secure_getenv ────────────────────────────────────────────────────────────
char *secure_getenv(const char *name) {
    return getenv(name);
}

// ── qsort_r ──────────────────────────────────────────────────────────────────
extern void qsort(void *base, size_t nmemb, size_t size,
                  int (*compar)(const void *, const void *));

// Single-threaded PD: a static carries the user comparator + context across the
// plain-qsort call. (No reentrancy hazard — the PD's rasterizer is single-threaded
// with LP_NUM_THREADS=0.)
static int (*g_qsort_r_cmp)(const void *, const void *, void *);
static void *g_qsort_r_ctx;

static int qsort_r_trampoline(const void *a, const void *b) {
    return g_qsort_r_cmp(a, b, g_qsort_r_ctx);
}

void qsort_r(void *base, size_t nmemb, size_t size,
             int (*compar)(const void *, const void *, void *), void *arg) {
    g_qsort_r_cmp = compar;
    g_qsort_r_ctx = arg;
    qsort(base, nmemb, size, qsort_r_trampoline);
}

// ── c23_timespec_get ─────────────────────────────────────────────────────────
// The C23-named entry the newer toolchain emits; forward to the libc timespec_get
// the seL4 musl provides (which reads the PD's zeroed clock — deterministic).
struct timespec; // opaque; the libc timespec_get takes (struct timespec*, int)
extern int timespec_get(struct timespec *ts, int base);
int c23_timespec_get(struct timespec *ts, int base) {
    return timespec_get(ts, base);
}

// ── pthread cancellation-point machinery (dead with LP_NUM_THREADS=0) ─────────
// The musl ABI: long __syscall_cp_asm(volatile int *cancel, long n, long a..f).
// With no cancellation, it is the plain syscall. __syscall is the seL4 musl's
// C-level syscall (routes via __sysinfo, NOT a direct svc).
extern long __syscall(long n, ...);

long __syscall_cp_asm(volatile int *cancel, long n,
                      long a, long b, long c, long d, long e, long f) {
    (void)cancel;
    return __syscall(n, a, b, c, d, e, f);
}

// The __cp_begin/__cp_end/__cp_cancel markers are address labels musl's
// cancellation asm compares the trap PC against. With the forwarding
// __syscall_cp_asm above (which never traps a cancellable point), they are never
// consulted; define them as distinct addresses so the references resolve.
__attribute__((used)) void __cp_begin(void) {}
__attribute__((used)) void __cp_end(void) {}
__attribute__((used)) void __cp_cancel(void) {}

// ── getrandom ────────────────────────────────────────────────────────────────
// The libc wrapper the leaner seL4 musl omits. Issue the raw syscall (#278 on
// aarch64); the PD's syscall handler zero-fills deterministically — fine, the
// offscreen render's randomness is not load-bearing.
#ifndef SYS_getrandom
#define SYS_getrandom 278
#endif
long getrandom(void *buf, size_t buflen, unsigned int flags) {
    return __syscall(SYS_getrandom, (long)buf, (long)buflen, (long)flags);
}

// ── memfd_create ─────────────────────────────────────────────────────────────
// Mesa's shader-cache / scratch paths reach for an anonymous memory fd. The PD
// has no filesystem, so report ENOSYS (-1, errno=38) — Mesa falls back to an
// ordinary anonymous mmap (which our handler serves), the headless-correct path.
extern int *__errno_location(void);
int memfd_create(const char *name, unsigned int flags) {
    (void)name; (void)flags;
    *__errno_location() = 38; // ENOSYS
    return -1;
}

// ── enable musl threads (THE gate before __clone) ────────────────────────────
// musl's `__pthread_create` (reached by lavapipe via thrd_create) returns -ENOSYS
// unless TWO startup steps that musl normally does in `__libc_start_main` ran —
// and the seL4 `sel4-root-task-with-std` runtime (which sets up TLS its OWN way)
// ran NEITHER:
//
//   (1) `__libc.can_do_threads = 1` — the gate at the very top of
//       `__pthread_create` (a load at struct offset 0; -ENOSYS if zero).
//   (2) `__libc.tls_head / tls_size / tls_align / tls_cnt` populated from the
//       PT_TLS program header — `__pthread_create` calls `__copy_tls()` to build
//       the new thread's TLS, which reads exactly those fields. With them zero,
//       `__copy_tls` computes a garbage thread pointer and FAULTS (the measured
//       `vm fault on data at -8` inside `__copy_tls`).
//
// We do BOTH here, replicating the field-population half of musl's
// `static_init_tls` (src/env/__init_tls.c) — scanning this image's program headers
// for PT_TLS and filling `__libc.tls_*` — but WITHOUT calling `__init_tp` on the
// main thread (its thread pointer is already set up by the seL4 runtime; we must
// not disturb it). `struct __libc` (this libc's libc.h):
//   int can_do_threads; int threaded; int secure; volatile int threads_minus_1;
//   size_t *auxv; struct tls_module *tls_head; size_t tls_size, tls_align, tls_cnt;
// → offsets: can_do_threads@0, threaded@4, tls_head@24, tls_size@32,
//   tls_align@40, tls_cnt@48 (matches the disassembly of __copy_tls in this libc).

#include <stdint.h>
#include <elf.h>

// `struct tls_module` (libc.h): next, image, len, size, align, offset.
struct dregg_tls_module {
    struct dregg_tls_module *next;
    void *image;
    size_t len, size, align, offset;
};

// `struct __libc` as a field-addressable view (only the fields we set).
struct dregg_libc_view {
    int can_do_threads;          // 0
    int threaded;                // 4
    int secure;                  // 8
    volatile int threads_minus_1;// 12
    size_t *auxv;                // 16
    struct dregg_tls_module *tls_head; // 24
    size_t tls_size, tls_align, tls_cnt; // 32, 40, 48
};
extern struct dregg_libc_view __libc;

// The ELF header at the image base (provided by the linker; the seL4 root-task
// image is loaded such that __ehdr_start is the Elf64_Ehdr).
extern const Elf64_Ehdr __ehdr_start;

// `sizeof(struct pthread)` for this libc — musl computes tls_size as
// `2*sizeof(void*) + sizeof(struct pthread) + main_tls.size + main_tls.align`
// rounded to MIN_TLS_ALIGN. We obtain sizeof(struct pthread) from the libc itself
// via the exported helper if present; else a safe upper bound. The seL4 musl
// exports `__pthread_self` but not the size, so we use musl's known aarch64
// `struct pthread` size as a conservative, page-padded reservation: the exact
// value only affects how much memory __copy_tls reserves, and __pthread_create
// mmaps `tls_size + guard + stack` — over-reserving TLS is safe. We use 2048,
// comfortably above aarch64 musl's `struct pthread` (~200 bytes) + DTV slack.
#define DREGG_PTHREAD_SIZE 2048u
#define DREGG_MIN_TLS_ALIGN (4u * sizeof(void *)) // musl MIN_TLS_ALIGN on aarch64

static struct dregg_tls_module dregg_main_tls;

// Populate __libc.tls_* from PT_TLS so __copy_tls builds a valid per-thread block.
static void dregg_init_libc_tls(void) {
    const Elf64_Ehdr *eh = &__ehdr_start;
    uintptr_t base = (uintptr_t)eh;
    const Elf64_Phdr *ph = (const Elf64_Phdr *)(base + eh->e_phoff);
    const Elf64_Phdr *tls = 0;
    // For a non-PIE static root-task image, p_vaddr is the absolute load address,
    // so the TLS image lives at p_vaddr directly (base offset 0). Match musl's
    // static_init_tls: base = AT_PHDR - PT_PHDR.p_vaddr (== 0 here).
    for (int i = 0; i < eh->e_phnum; i++) {
        if (ph[i].p_type == PT_TLS) tls = &ph[i];
    }
    if (!tls) return; // no TLS segment: nothing to set (threads w/o TLS still work)

    dregg_main_tls.image  = (void *)(uintptr_t)tls->p_vaddr;
    dregg_main_tls.len    = tls->p_filesz;
    dregg_main_tls.size   = tls->p_memsz;
    dregg_main_tls.align  = tls->p_align ? tls->p_align : 1;
    __libc.tls_cnt  = 1;
    __libc.tls_head = &dregg_main_tls;

    // musl: round the TLS size for alignment (variant-I / TLS_ABOVE_TP on aarch64).
    dregg_main_tls.size += (-dregg_main_tls.size - (uintptr_t)dregg_main_tls.image)
                           & (dregg_main_tls.align - 1);
    if (dregg_main_tls.align < DREGG_MIN_TLS_ALIGN)
        dregg_main_tls.align = DREGG_MIN_TLS_ALIGN;

    __libc.tls_align = dregg_main_tls.align;
    __libc.tls_size  = (2 * sizeof(void *) + DREGG_PTHREAD_SIZE
                        + dregg_main_tls.size + dregg_main_tls.align
                        + DREGG_MIN_TLS_ALIGN - 1) & -DREGG_MIN_TLS_ALIGN;
}

void dregg_enable_musl_threads(void) {
    __libc.can_do_threads = 1; // pass the __pthread_create gate
    __libc.threaded = 1;
    dregg_init_libc_tls();     // make __copy_tls produce a valid TLS block
}

// ── __clone (THE submit-thread lever) ────────────────────────────────────────
// The seL4/musllibc fork's `__clone` for the `aarch64_sel4` ARCH is a STUB that
// returns -ENOSYS without issuing any syscall (`mov w0,#-38; ret`). lavapipe's
// `lvp_queue_init` reaches it (thrd_create -> pthread_create -> __clone) and the
// -ENOSYS surfaces as `vkCreateDevice = VK_ERROR_UNKNOWN`. We OVERRIDE `__clone`
// here (whole-archived ⇒ chosen over libc's `clone.o`, which lld then never pulls,
// exactly as with `getenv` above) and forward to the Rust `dregg_clone`
// (src/thread.rs), which materializes a real seL4 TCB sharing this PD's CSpace +
// VSpace. The ABI is musl's __clone(fn, stack, flags, arg, ptid, tls, ctid).
extern long dregg_clone(long fn, long stack, long flags, long arg,
                        long ptid, long tls, long ctid);
int __clone(int (*fn)(void *), void *stack, int flags, void *arg,
            void *ptid, void *tls, void *ctid) {
    return (int) dregg_clone((long)fn, (long)stack, (long)flags, (long)arg,
                             (long)ptid, (long)tls, (long)ctid);
}

// ── dlopen/dlsym/dlerror (THE JIT-init lever) ────────────────────────────────
// LLVM's MCJIT engine creation (EngineBuilder::create, reached by gallivm's
// lp_build_create_jit_compiler_for_module) calls
// `sys::DynamicLibrary::LoadLibraryPermanently(nullptr)` → `::dlopen(NULL,
// RTLD_LAZY|RTLD_GLOBAL)` to make THIS program's symbols resolvable by the JIT.
// The seL4/musllibc fork ships a `dlopen` STUB that returns NULL with
// dlerror()="Dynamic loading not supported" (measured via the llvm-target-diag
// MCJIT probe: "MCJIT create FAILED: Dynamic loading not supported"). That NULL
// makes create() return NULL, and gallivm then dereferences the NULL engine
// (JIT->setObjectCache) → the vm-fault-at-0 wall.
//
// The process-handle dlopen is the ONLY thing LLVM needs here: a handle that
// stands for "this image", against which it can dlsym runtime symbols. We override
// (whole-archived ⇒ chosen over the libc's weak `dlopen.o`, exactly as `__clone`/
// `getenv` above):
//   * dlopen(NULL, …)  → a non-NULL sentinel (the process handle). The fully-static
//     PD IS its own symbol space; there is nothing to actually load.
//   * dlopen(name, …)  → NULL (no filesystem; LLVM never opens a named library on
//     this path — it only ever asks for the process handle here).
//   * dlsym(handle, …) → NULL. The seL4-musl image carries no runtime symbol table,
//     so a process-handle lookup honestly finds nothing; LLVM's RuntimeDyld first
//     consults its explicit-symbol map + the static special-symbols, so the empty
//     compute shader (no external refs) resolves without dlsym. A real shader that
//     needs an unregistered runtime symbol will surface as a PRECISE later wall
//     (an unresolved-symbol relocation), not this fatal create() NULL.
//   * dlerror() → NULL (no error pending after the successful process-handle open).
static char dregg_process_handle; // a unique, stable, non-NULL sentinel address
void *dlopen(const char *file, int flags) {
    (void)flags;
    if (file == NULL) return (void *)&dregg_process_handle; // the process handle
    return NULL; // no named-library loading in a static PD
}
void *dlsym(void *handle, const char *symbol) {
    (void)handle; (void)symbol;
    return NULL; // no runtime symbol table; RuntimeDyld's other paths cover the rest
}
char *dlerror(void) {
    return NULL; // no pending error after a successful process-handle dlopen
}
int dlclose(void *handle) {
    (void)handle;
    return 0; // the process handle is never really closed
}

// ── reallocarray ─────────────────────────────────────────────────────────────
// realloc(ptr, nmemb*size) with multiplication-overflow protection (the BSD/glibc
// extension util/ code uses). The seL4 musl ships realloc but not this wrapper.
extern void *realloc(void *ptr, size_t size);
void *reallocarray(void *ptr, size_t nmemb, size_t size) {
    if (size != 0 && nmemb > (size_t)-1 / size) {
        *__errno_location() = 12; // ENOMEM
        return NULL;
    }
    return realloc(ptr, nmemb * size);
}
