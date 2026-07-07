//! serve-bench — attribute the per-call cost of the leanc-compiled proven serve.
//!
//! Links `libdrorb.a` (the exact archive the dataplane host links) and calls the
//! exported `drorb_serve` (`ByteArray -> ByteArray`) in a tight single-threaded
//! loop over fixed requests. Only `drorb_serve` is exported, so the per-phase
//! breakdown is COARSE — an A/B over input variants, not an internal profiler.
//! Each lever is labelled with what it does and does not isolate.
//!
//! Levers:
//!   * FFI floor           — wrap the request bytes in a Lean ByteArray and drop
//!                           it, no serve call: the marshalling boundary cost.
//!   * /health full        — the whole pipeline on a fixed `GET /health` (200).
//!   * /admin short-circuit— `GET /admin` with no bearer: the JWT gate (stage 1)
//!                           runs its FSM and short-circuits stages 2..13 to a 401.
//!   * unknown route (404) — full 13-stage fold, different route than /health.
//!   * parse-size slope    — /health with K bytes of extra header padding, at a
//!                           few K, to read ns/byte of the request-ingest/parse.
//!
//! Report is ns/call (min + median over trials) for each lever, then derived
//! buckets and the single biggest one.

use std::time::Instant;

#[repr(C)]
struct LeanObject {
    _private: [u8; 0],
}

unsafe extern "C" {
    fn lean_initialize_runtime_module();
    fn lean_io_mark_end_initialization();
    fn initialize_Dataplane(builtin: u8, world: *mut LeanObject) -> *mut LeanObject;
    fn drorb_serve(input: *mut LeanObject) -> *mut LeanObject;

    fn drorb_sarray_of_bytes(p: *const u8, n: usize) -> *mut LeanObject;
    fn drorb_sarray_len(o: *mut LeanObject) -> usize;
    fn drorb_sarray_ptr(o: *mut LeanObject) -> *const u8;
    fn drorb_obj_dec(o: *mut LeanObject);
    fn drorb_io_world() -> *mut LeanObject;
    fn drorb_io_ok(o: *mut LeanObject) -> i32;
}

fn lean_boot() {
    unsafe {
        lean_initialize_runtime_module();
        let res = initialize_Dataplane(1, drorb_io_world());
        if drorb_io_ok(res) == 0 {
            panic!("initialize_Dataplane returned an IO error");
        }
        drorb_obj_dec(res);
        lean_io_mark_end_initialization();
    }
}

/// One full seam crossing: marshal `req` in, serve, copy the response length out,
/// drop the response. Returns the response length so the optimizer cannot elide
/// the work and so we can sanity-check the status.
#[inline(never)]
fn serve_once(req: &[u8], out: &mut Vec<u8>) -> usize {
    unsafe {
        let input = drorb_sarray_of_bytes(req.as_ptr(), req.len());
        let output = drorb_serve(input);
        let len = drorb_sarray_len(output);
        out.clear();
        out.extend_from_slice(std::slice::from_raw_parts(drorb_sarray_ptr(output), len));
        drorb_obj_dec(output);
        len
    }
}

/// The FFI marshalling floor: wrap the bytes in a Lean ByteArray and drop it,
/// with no serve call. Lower bound on the per-call boundary cost.
#[inline(never)]
fn marshal_floor(req: &[u8]) -> usize {
    unsafe {
        let input = drorb_sarray_of_bytes(req.as_ptr(), req.len());
        let n = drorb_sarray_len(input);
        drorb_obj_dec(input);
        n
    }
}

/// Median of a small set of per-call ns measurements.
fn median(mut v: Vec<f64>) -> f64 {
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let n = v.len();
    if n % 2 == 1 {
        v[n / 2]
    } else {
        (v[n / 2 - 1] + v[n / 2]) / 2.0
    }
}

/// Time `f` over `n` iterations, `trials` times; return (min ns/call, median ns/call).
fn bench<F: FnMut() -> usize>(n: u64, trials: usize, mut f: F) -> (f64, f64) {
    // warmup
    let mut acc = 0usize;
    for _ in 0..(n / 10 + 1) {
        acc = acc.wrapping_add(f());
    }
    let mut per_call = Vec::with_capacity(trials);
    for _ in 0..trials {
        let t = Instant::now();
        for _ in 0..n {
            acc = acc.wrapping_add(f());
        }
        let ns = t.elapsed().as_nanos() as f64 / n as f64;
        per_call.push(ns);
    }
    std::hint::black_box(acc);
    let min = per_call.iter().cloned().fold(f64::INFINITY, f64::min);
    (min, median(per_call))
}

/// `GET <target> HTTP/1.1` with a Host header and `pad` bytes of extra header
/// value, terminated by the blank line.
fn http_get(target: &str, pad: usize) -> Vec<u8> {
    let mut s = format!("GET {target} HTTP/1.1\r\nHost: bench.local\r\n");
    if pad > 0 {
        s.push_str("X-Pad: ");
        s.push_str(&"a".repeat(pad));
        s.push_str("\r\n");
    }
    s.push_str("\r\n");
    s.into_bytes()
}

/// First line of a response, for a status sanity-check.
fn status_line(bytes: &[u8]) -> String {
    let end = bytes.iter().position(|&b| b == b'\r').unwrap_or(bytes.len().min(40));
    String::from_utf8_lossy(&bytes[..end]).into_owned()
}

fn main() {
    let n: u64 = std::env::args()
        .nth(1)
        .and_then(|a| a.parse().ok())
        .unwrap_or(100_000);
    let trials: usize = std::env::args()
        .nth(2)
        .and_then(|a| a.parse().ok())
        .unwrap_or(7);

    lean_boot();

    let health = http_get("/health", 0);
    let admin = http_get("/admin", 0);
    let unknown = http_get("/nope", 0);

    // Sanity: show the status each request actually serves, so the A/B is honest.
    let mut out = Vec::new();
    for (name, req) in [("/health", &health), ("/admin", &admin), ("/nope", &unknown)] {
        serve_once(req, &mut out);
        println!(
            "sanity {name:<9} -> {} ({} resp bytes)",
            status_line(&out),
            out.len()
        );
    }
    println!("N={n} iters/trial, {trials} trials\n");

    // Levers.
    let mut ob = Vec::new();
    let (mf_min, mf_med) = bench(n, trials, || marshal_floor(&health));
    let (h_min, h_med) = bench(n, trials, || serve_once(&health, &mut ob));
    let (a_min, a_med) = bench(n, trials, || serve_once(&admin, &mut ob));
    let (u_min, u_med) = bench(n, trials, || serve_once(&unknown, &mut ob));

    println!("{:<26} {:>12} {:>12}", "lever", "min ns/call", "med ns/call");
    println!("{}", "-".repeat(52));
    let row = |name: &str, mn: f64, md: f64| println!("{name:<26} {mn:>12.1} {md:>12.1}");
    row("FFI marshal floor", mf_min, mf_med);
    row("/health full (200)", h_min, h_med);
    row("/admin short-circuit(401)", a_min, a_med);
    row("/nope full (404)", u_min, u_med);

    // Size sensitivity: does the per-call cost grow with request size on the
    // SUCCESS path (/health, runs handler + all transforms) or on the
    // SHORT-CIRCUIT path (/nope, gated before the handler)? Small N here because
    // padded success-path calls get expensive fast.
    let sn = (n / 20).max(2000);
    println!("\nsize sensitivity (min ns/call, N={sn}):");
    println!("{:<10} {:>12} {:>14} {:>14}", "pad", "req bytes", "/health(200)", "/nope(403)");
    let mut pts: Vec<(f64, f64)> = Vec::new();
    for pad in [0usize, 64, 128, 256, 512, 1024] {
        let hreq = http_get("/health", pad);
        let nreq = http_get("/nope", pad);
        let (hmn, _) = bench(sn, trials, || serve_once(&hreq, &mut ob));
        let (nmn, _) = bench(sn, trials, || serve_once(&nreq, &mut ob));
        println!("{:<10} {:>12} {:>14.1} {:>14.1}", pad, hreq.len(), hmn, nmn);
        pts.push((hreq.len() as f64, hmn));
    }
    // Least-squares slope ns per input byte.
    let k = pts.len() as f64;
    let sx: f64 = pts.iter().map(|p| p.0).sum();
    let sy: f64 = pts.iter().map(|p| p.1).sum();
    let sxx: f64 = pts.iter().map(|p| p.0 * p.0).sum();
    let sxy: f64 = pts.iter().map(|p| p.0 * p.1).sum();
    let slope = (k * sxy - sx * sy) / (k * sxx - sx * sx);
    let intercept = (sy - slope * sx) / k;
    println!("  fit: ~{slope:.3} ns/input-byte, intercept ~{intercept:.0} ns");

    // Derived buckets (min ns/call).
    println!("\nderived buckets (min ns/call):");
    println!("  FFI boundary               : {mf_min:>10.1}");
    println!("  serve compute (health-FFI) : {:>10.1}", h_min - mf_min);
    let parse_health = slope * health.len() as f64;
    println!(
        "  ├ parse/ingest @{} B (~slope): {:>10.1}",
        health.len(),
        parse_health
    );
    println!(
        "  └ 13-stage fold + handler + serialize + obs (health - FFI - parse): {:>10.1}",
        h_min - mf_min - parse_health
    );
    println!(
        "  stages 2..13 + handler (health - admin short-circuit): {:>10.1}",
        h_min - a_min
    );
}
