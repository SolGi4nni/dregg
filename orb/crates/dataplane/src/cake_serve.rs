//! Alternative serve path: answer requests from certified export-function
//! machine code linked into this process, instead of the leanc-compiled proven
//! serve.
//!
//! The linked object (`ffi/cake/serve.S`, driven by the re-entrant
//! `cake_serve_ffi.c`) is a compiled export function: its runtime is initialised
//! once per image (`cake_serve_init_shard`, main-return so it returns to us) and
//! then `serve` is an ordinary SysV-ABI symbol called per request. The response
//! bytes are produced by the machine code and are byte-identical to the
//! validated standalone harness for the same request.
//!
//! Present only when `ffi/cake/libcakeserve.a` is linked (build.rs links it when
//! it exists, setting `cfg(drorb_cake_serve)`), which is the demo build. Gated at
//! runtime behind `DRORB_CAKE_SERVE=1`, so the default path is untouched: every
//! non-demo build and every unset-flag run falls through to the deployed leanc
//! pipeline.
//!
//! ## All routes
//!
//! When enabled, EVERY HTTP request (any method/target — not just `GET /`) is
//! handed to the fused export-function `serve`. The compiled pipeline parses the
//! start-line and returns its redirect+HSTS response; a request it cannot answer
//! comes back as 0 bytes and the caller falls through to leanc. Non-HTTP wire
//! bytes (they never reach this plaintext serve seam) are not routed here.
//!
//! ## Per-shard heaps (parallel-safe)
//!
//! The emitted object keeps its heap/stack region and saved runtime state in
//! fixed-address words, so one image is single-threaded. To let N reactor shards
//! (serve owners, or blocking serve threads) serve in PARALLEL, the linked
//! object provides N symbol-disjoint IMAGES (see `cake_serve_ffi.c`). Each shard
//! thread claims one image index on first use and drives only that image, so no
//! two threads ever touch the same runtime state — the calls run concurrently
//! with no lock. A thread that arrives after the image pool is exhausted gets no
//! image and falls through to leanc (a named residual, not a correctness risk).

/// HTTP request methods this alternative path will route to the compiled serve.
/// Any request whose start-line begins with one of these (followed by a space)
/// is handed to the fused export function; the compiled pipeline decides what it
/// can answer. Non-HTTP bytes match nothing and are never routed.
#[cfg(drorb_cake_serve)]
const HTTP_METHODS: [&[u8]; 9] = [
    b"GET ",
    b"HEAD ",
    b"POST ",
    b"PUT ",
    b"DELETE ",
    b"OPTIONS ",
    b"PATCH ",
    b"TRACE ",
    b"CONNECT ",
];

/// Does `line` begin like an HTTP/1.x request line (a known method token
/// followed by a space)? Cheap, allocation-free.
#[cfg(drorb_cake_serve)]
#[inline]
fn looks_like_http_request(line: &[u8]) -> bool {
    HTTP_METHODS.iter().any(|m| line.starts_with(m))
}

/// The request bytes a serve job carries can be either the raw wire request (the
/// blocking path) or a cfg-FRAMED request (`cfgLen(4 BE) :: config :: request` —
/// the io_uring `ServeCfg` seam, `cfgLen = 0` for the empty-config default). Peel
/// an optional leading cfg frame and return the start of the actual request, so
/// the route predicate and the serve see the same bytes on both paths. Returns
/// the input unchanged when it already begins with the request (no frame).
#[cfg(drorb_cake_serve)]
#[inline]
fn unframe(req: &[u8]) -> &[u8] {
    if looks_like_http_request(req) {
        return req; // raw request (blocking path)
    }
    if req.len() >= 4 {
        let cfg_len = u32::from_be_bytes([req[0], req[1], req[2], req[3]]) as usize;
        if let Some(off) = cfg_len.checked_add(4) {
            if off <= req.len() && looks_like_http_request(&req[off..]) {
                return &req[off..]; // cfg-framed request (io_uring ServeCfg seam)
            }
        }
    }
    req
}

#[cfg(drorb_cake_serve)]
unsafe extern "C" {
    /// `size_t cake_serve_http_shard(int idx, const uint8_t* req, size_t req_len,
    /// uint8_t* out, size_t out_cap)` — stage the control block and run per-shard
    /// image `idx`'s compiled export function once, in-process. Returns response
    /// bytes written into `out` (0 on a broken precondition or an unavailable
    /// image, so the caller falls through to leanc). Distinct `idx` values are
    /// independent runtimes and may run concurrently on different threads.
    fn cake_serve_http_shard(
        idx: std::os::raw::c_int,
        req: *const u8,
        req_len: usize,
        out: *mut u8,
        out_cap: usize,
    ) -> usize;
    /// Number of parallel per-shard images the linked object provides.
    fn cake_image_count() -> std::os::raw::c_int;
    /// PROVENANCE counter, incremented once per serve that returns a response.
    /// Nonzero after a request proves the compiled machine code ran on it.
    static cake_serve_report_count: u64;
}

/// Whether `DRORB_CAKE_SERVE` routes requests to the compiled serve.
/// Default OFF (unset ⇒ nothing changes). Read once; `1`/`true`/`yes`/`on` enable.
#[cfg(drorb_cake_serve)]
fn cake_serve_enabled() -> bool {
    use std::sync::OnceLock;
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| {
        std::env::var("DRORB_CAKE_SERVE")
            .map(|v| matches!(v.as_str(), "1" | "true" | "yes" | "on"))
            .unwrap_or(false)
    })
}

/// This thread's per-shard image index, claimed once from a process-global pool
/// on first use. `-1` means "no image left" (the pool was exhausted); such a
/// thread never uses the compiled path and always falls through to leanc.
#[cfg(drorb_cake_serve)]
fn my_image_idx() -> std::os::raw::c_int {
    use std::cell::Cell;
    use std::os::raw::c_int;
    use std::sync::atomic::{AtomicUsize, Ordering};
    thread_local! {
        // -2 = unclaimed sentinel; set to a real index or -1 on first read.
        static IDX: Cell<c_int> = const { Cell::new(-2) };
    }
    IDX.with(|c| {
        let v = c.get();
        if v != -2 {
            return v;
        }
        // SAFETY: plain read of a linked C function returning the image count.
        let n = unsafe { cake_image_count() } as usize;
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let claimed = NEXT.fetch_add(1, Ordering::Relaxed);
        let idx = if claimed < n { claimed as c_int } else { -1 };
        c.set(idx);
        idx
    })
}

/// Cheap, allocation-free predicate: would `req` be routed to the compiled path?
/// (enabled AND its start-line is an HTTP request line). Lets a caller skip
/// taking a response buffer on the default path — zero per-request overhead when
/// the demo is off.
#[cfg(drorb_cake_serve)]
#[inline]
pub(crate) fn wants_cake_serve(req: &[u8]) -> bool {
    cake_serve_enabled() && looks_like_http_request(unframe(req))
}

/// Non-demo builds: the compiled path is absent, so this is a compile-time `false`.
#[cfg(not(drorb_cake_serve))]
#[inline]
pub(crate) fn wants_cake_serve(_req: &[u8]) -> bool {
    false
}

/// If the compiled serve is enabled AND `req` is an HTTP request, answer it from
/// the certified export-function machine code (no Lean seam crossing) on this
/// thread's own per-shard image, and return `true`. Otherwise leave `out`
/// untouched and return `false` so the caller runs the deployed leanc pipeline.
/// Safe to call concurrently from many shard threads (each drives its own image).
#[cfg(drorb_cake_serve)]
pub(crate) fn serve_cake_into(req: &[u8], out: &mut Vec<u8>) -> bool {
    if !wants_cake_serve(req) {
        return false;
    }
    let idx = my_image_idx();
    if idx < 0 {
        return false; // image pool exhausted on this thread — fall through
    }
    out.clear();
    out.resize(4096, 0);
    // SAFETY: `req` is a valid read-only slice; `out` is a live owned buffer of
    // `out.len()` bytes. `cake_serve_http_shard` stages its own control/request
    // scratch, calls image `idx`'s export function once, and copies at most
    // `out.len()` response bytes into `out`. `idx` is this thread's exclusive
    // image, so the call never races another thread's runtime state.
    let line = unframe(req);
    let n = unsafe {
        cake_serve_http_shard(idx, line.as_ptr(), line.len(), out.as_mut_ptr(), out.len())
    };
    out.truncate(n);
    if n == 0 {
        return false; // compiled path declined — fall through to leanc
    }
    // PROVENANCE: the compiled machine code ran to a response; surface the counter.
    // SAFETY: plain relaxed read of an atomically-updated C global.
    let served = unsafe { cake_serve_report_count };
    eprintln!(
        "dataplane: request answered by certified export-function machine \
         code (image {idx}, {n} bytes, cake_serve fired {served} times)"
    );
    true
}

/// Non-demo builds (no `libcakeserve.a` linked): the compiled path is absent, so
/// this is a compile-time no-op and every request runs the leanc pipeline.
#[cfg(not(drorb_cake_serve))]
#[inline]
pub(crate) fn serve_cake_into(_req: &[u8], _out: &mut Vec<u8>) -> bool {
    false
}
