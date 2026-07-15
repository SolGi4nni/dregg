//! The effect/continuation interpreter loop: a DUMB executor for the proven
//! resumable serve.
//!
//! The proven core (`Reactor.ServeStep.serveStep`, exported as `drorb_serve_step`)
//! is a resumable state machine. It runs pure until it needs one I/O result the
//! sans-IO core cannot produce, then YIELDS an `Effect` carrying everything the
//! shell needs to perform that I/O plus a continuation. This loop is the shell:
//! it crosses `drorb_serve_step`, and
//!
//!   * on DONE — writes the response bytes and stops;
//!   * on YIELD `proxyDial(backend, req)` — dials the backend the PROVEN pick
//!     chose, forwards `req`, and threads the upstream reply back through
//!     `drorb_serve_resume`, whose continuation runs the FULL response-transform
//!     fold (cors / gzip / security-headers / header) over the reply;
//!   * on YIELD `cacheLookup(key)` — probes the process-global store at the
//!     PROVEN key; a fresh HIT returns its gate-admitted bytes (the core's
//!     continuation `.done`s them WITHOUT running the handler), a MISS returns
//!     empty (the core runs the fold, then yields `cacheStore`);
//!   * on YIELD `cacheStore(key, resp, lifetime)` — stores `resp` under the
//!     PROVEN key + lifetime, then resumes to the final `.done`.
//!
//! The interpreter decides NOTHING about a request's meaning: whether to proxy,
//! which backend, whether/what/how-long to cache, and what to do with the reply
//! are all the proven core's. The shell only opens sockets and moves bytes.
//!
//! ## The FFI continuation marshalling (multi-effect replay)
//!
//! No Lean closure crosses the FFI. The step export returns a tagged `Step`; on a
//! yield the shell executes the effect, appends its result to a GROWING list, and
//! crosses the resume export with the ORIGINAL `(mask, request)` plus that list.
//! The proven core REPLAYS `serveStep` (pure ⇒ deterministic), feeds each recorded
//! result into successive continuations, and returns the next `Step` — which the
//! shell re-encodes and either writes (`.done`) or drives one more effect. A cache
//! HIT is one lookup; a cache MISS is lookup → store → done; a proxy is one dial.

use std::sync::mpsc::{Receiver, Sender};

use crate::pool::PooledBuf;
use crate::proxy_dial::{self, Fleet};
use crate::serve::{Seam, ServeGateway};

/// Step-result tag: the serve is DONE, the rest of the output is the response.
pub(crate) const TAG_DONE: u8 = 0;
/// Step-result tag: YIELDED `proxyDial` — byte 1 is the proven-chosen backend id,
/// bytes 2.. are the request to forward.
pub(crate) const TAG_YIELD_PROXY: u8 = 1;
/// Step-result tag: YIELDED `cacheLookup` — bytes 1.. are the proven cache key.
pub(crate) const TAG_YIELD_CACHE_LOOKUP: u8 = 2;
/// Step-result tag: YIELDED `cacheStore` — byte layout
/// `[1] lifetime(4 BE) :: keyLen(4 BE) :: key :: resp`.
pub(crate) const TAG_YIELD_CACHE_STORE: u8 = 3;

/// Is the effect/continuation seam enabled? Gated behind `DRORB_EFFECT_SEAM=1` so
/// the seam is opt-in and the default path stays on the established hooks + metered
/// serve until the reconcile owner promotes it.
pub fn enabled() -> bool {
    std::env::var("DRORB_EFFECT_SEAM")
        .map(|v| v == "1")
        .unwrap_or(false)
}

/// A conservative host-side ROUTING PREFILTER (not the decision): should this
/// request be offered to the effect seam at all? The proven core still makes the
/// real proxy/cache/gate decision; this only avoids crossing the seam for the
/// non-proxy, non-cacheable bulk (which the metered serve handles with its real
/// IP-filter / rate gates). Mirrors the core's cacheable-route shape (a GET under
/// `/static` or `/admin`) plus the proxy route, so the seam is consulted for
/// exactly the requests it can act on.
pub fn should_handle(req: &[u8]) -> bool {
    if crate::proxy_hook::is_proxy_path(req) && fleet().is_some() {
        return true;
    }
    is_cacheable_shape(req)
}

/// GET whose target sits under `/static` or `/admin` — the cacheable-route shape
/// the core's `isCacheableTarget` decides on. A prefilter only: the core re-derives
/// this and owns the actual cacheability decision — including RFC 7232 conditional
/// revalidation on the cache path (`Reactor.ServeStep.revalidate`, applied by
/// `cacheResume` on both HIT and MISS) and the RFC 7233 Range refusal (`hasRange`
/// inside the proven `cacheableKey`). Conditional and Range requests therefore
/// cross the seam and the PROVEN core decides them: a conditional GET is answered
/// 304/412 from the cache path (cache-fast, handler not run on a HIT), a ranged
/// GET is declined by the core's cache decision and served by the fold (206/416).
fn is_cacheable_shape(req: &[u8]) -> bool {
    let line_end = match find(req, b"\r\n") {
        Some(e) => e,
        None => return false,
    };
    let line = &req[..line_end];
    let mut parts = line.split(|&b| b == b' ');
    if parts.next() != Some(b"GET") {
        return false;
    }
    match parts.next() {
        Some(t) => t.starts_with(b"/static") || t.starts_with(b"/admin"),
        None => false,
    }
}

/// The deployment LB-policy selector the running step dials with, read from
/// `DRORB_LB_POLICY`. `0` (unset / `default` / `rendezvous`) is the deployed
/// default chain — the STEP crosses `drorb_serve_step`, byte-identical. `1`
/// (`leastConn`) selects `altDeployment`'s least-connections `api` pool — the STEP
/// crosses the config-driven `drorb_serve_step_cfg`, so a proxied request reaches
/// the backend the config-declared LB policy selects.
pub fn lb_selector() -> u8 {
    match std::env::var("DRORB_LB_POLICY").ok().as_deref() {
        Some("leastConn") | Some("least_conn") | Some("leastconn") | Some("1") => 1,
        _ => 0,
    }
}

/// The live health/breaker bitmask the proven proxy pick reads; `0` when no fleet
/// is configured (a cache/plain request needs no backends). Shared with the async
/// io_uring step path so it frames the SAME mask the blocking interpreter does.
pub fn current_mask() -> u8 {
    fleet().map(|f| f.mask()).unwrap_or(0)
}

/// The step/resume seams and framing prefix the running deployment dials with — the
/// SAME selection [`run_effect_serve`] makes, factored out so the async io_uring
/// step path (`uring::submit_step` / `uring::submit_resume`) crosses the identical
/// seam pair and threads the identical prefix. See `run_effect_serve` for the
/// selection rationale (config-policy seams under `DRORB_CONFIG`, else the legacy
/// `DRORB_LB_POLICY` selector).
pub fn seams() -> (Seam, Seam, Option<u8>) {
    if let Some(dep) = crate::config::get() {
        (
            Seam::ServeStepPol,
            Seam::ServeResumePol,
            Some(dep.lb_policy),
        )
    } else {
        let sel = lb_selector();
        if sel == 0 {
            (Seam::ServeStep, Seam::ServeResume, None)
        } else {
            (Seam::ServeStepCfg, Seam::ServeResumeCfg, Some(sel))
        }
    }
}

/// Frame the step input the proven core decodes: `mask :: request` (default) or
/// `prefix :: mask :: request` (a selector / LB-policy byte, when present).
pub(crate) fn frame_step(prefix: Option<u8>, mask: u8, req: &[u8], buf: &mut PooledBuf) {
    buf.clear();
    if let Some(p) = prefix {
        buf.push(p);
    }
    buf.push(mask);
    buf.extend_from_slice(req);
}

/// Frame the resume input: `[prefix ::] mask :: reqLen(4 BE) :: request :: count ::
/// (resultLen(4 BE) :: result)*`, so the proven core recovers `(mask, request)` to
/// replay plus the GROWING list of recorded effect results.
pub(crate) fn frame_resume(
    prefix: Option<u8>,
    mask: u8,
    req: &[u8],
    results: &[Vec<u8>],
    buf: &mut PooledBuf,
) {
    buf.clear();
    if let Some(p) = prefix {
        buf.push(p);
    }
    buf.push(mask);
    buf.extend_from_slice(&(req.len() as u32).to_be_bytes());
    buf.extend_from_slice(req);
    buf.push(results.len() as u8);
    for r in results {
        buf.extend_from_slice(&(r.len() as u32).to_be_bytes());
        buf.extend_from_slice(r);
    }
}

/// Run the proven resumable serve to completion for one request, executing every
/// yielded effect. Returns the final response bytes, or `None` when the request is
/// not one the seam acts on (so the caller falls through to the metered serve) or
/// the serve thread is gone.
pub fn run_effect_serve(
    req: &[u8],
    gw: &ServeGateway,
    reply_tx: &Sender<PooledBuf>,
    reply_rx: &Receiver<PooledBuf>,
) -> Option<Vec<u8>> {
    // The mask is the live health/breaker bitmask the proven proxy pick reads; 0
    // when no fleet is configured (a cache/plain request needs no backends).
    let mask = current_mask();

    // Choose the step/resume seams and the framing prefix (see `seams`):
    //  * an ARBITRARY operator config (DRORB_CONFIG, parsed at boot) drives the
    //    config-POLICY seams (`ServeStepPol`/`ServeResumePol`), threading the parsed
    //    pool's LB-policy byte — the running dial runs the config's declared policy;
    //  * else the legacy `DRORB_LB_POLICY` selector: `0` the default step/resume
    //    (byte-identical), non-zero the named-deployment config seams.
    let (step_seam, resume_seam, prefix) = seams();

    // 1. STEP: ask the proven core what to do with this request.
    let mut step_in = gw.pool().take();
    frame_step(prefix, mask, req, &mut step_in);
    let mut cur = gw.call_seam(step_in, step_seam, reply_tx, reply_rx)?;

    // The recorded effect results, threaded (and grown) across resume replays.
    let mut results: Vec<Vec<u8>> = Vec::new();

    loop {
        match cur.first().copied() {
            // DONE: the core produced the full response (a plain serve, a cache
            // HIT's stored bytes, a gate refusal, or a completed miss/proxy).
            Some(TAG_DONE) => return Some(cur[1..].to_vec()),

            // YIELD proxyDial: dial the proven-chosen backend and forward.
            Some(TAG_YIELD_PROXY) if cur.len() >= 2 => {
                let backend = cur[1] as u32;
                let forward_req = cur[2..].to_vec();
                let fleet = fleet()?; // a proxy yield with no fleet: fall through
                eprintln!(
                    "dataplane: serveStep YIELDED proxyDial(backend={backend}) (proven core chose the backend)"
                );
                let upstream = match fleet.addr(backend) {
                    Some(addr) => match proxy_dial::forward(addr, &forward_req, dial_timeout()) {
                        Ok(resp) => {
                            fleet.record_success(backend);
                            resp
                        }
                        Err(_) => {
                            fleet.record_failure(backend);
                            proxy_dial::bad_gateway()
                        }
                    },
                    None => proxy_dial::bad_gateway(),
                };
                results.push(upstream);
            }

            // YIELD cacheLookup: probe the store at the proven key, coalescing
            // concurrent same-key misses. A HIT (fresh entry) or a coalesced
            // WAITER (served the in-flight leader's single fetch) returns the
            // gate-admitted bytes stamped X-Cache: HIT (the core's continuation
            // .done's them without the handler); a LEADER on a cold key returns
            // empty (the core runs the fold, then yields cacheStore, whose store
            // publishes the fetch to every coalesced waiter).
            Some(TAG_YIELD_CACHE_LOOKUP) => {
                let key = &cur[1..];
                match crate::cache::global().lookup_coalescing(key) {
                    Some(hit) => {
                        eprintln!(
                            "dataplane: serveStep YIELDED cacheLookup -> HIT/coalesced (handler NOT run)"
                        );
                        results.push(hit);
                    }
                    None => {
                        // HOT miss (this caller leads the cold key). Consult the
                        // durable COLD tier before running the fold: a fresh disk
                        // entry is promoted into the hot tier (waking any coalesced
                        // waiters) and served stamped X-Cache: HIT — the handler is
                        // NOT run. Gated by DRORB_DISK_CACHE (else a no-op miss).
                        let disk = crate::cache_disk::global();
                        match if disk.enabled() {
                            disk.promote_on_miss(key, crate::cache_disk::now_secs())
                        } else {
                            None
                        } {
                            Some(hit) => {
                                eprintln!(
                                    "dataplane: serveStep YIELDED cacheLookup -> COLD-tier HIT (promoted, handler NOT run)"
                                );
                                results.push(hit);
                            }
                            None => {
                                eprintln!(
                                    "dataplane: serveStep YIELDED cacheLookup -> MISS/leader (core runs the fold once)"
                                );
                                results.push(Vec::new());
                            }
                        }
                    }
                }
            }

            // YIELD cacheStore: store the fold output under the proven key + lifetime.
            Some(TAG_YIELD_CACHE_STORE) if cur.len() >= 9 => {
                let lifetime = u32::from_be_bytes([cur[1], cur[2], cur[3], cur[4]]) as u64;
                let key_len = u32::from_be_bytes([cur[5], cur[6], cur[7], cur[8]]) as usize;
                let key_end = 9 + key_len;
                if cur.len() < key_end {
                    return None;
                }
                let key = cur[9..key_end].to_vec();
                let resp = cur[key_end..].to_vec();
                eprintln!(
                    "dataplane: serveStep YIELDED cacheStore(lifetime={lifetime}s, {} body bytes)",
                    resp.len()
                );
                crate::cache::global().store(&key, &resp, lifetime);
                // Also write the durable COLD tier so the entry survives a
                // restart (gated by DRORB_DISK_CACHE; a no-op otherwise). The
                // proven core already decided cacheability/key/lifetime.
                let disk = crate::cache_disk::global();
                if disk.enabled()
                    && lifetime != 0
                    && let Err(e) = disk.put(&key, &resp, crate::cache_disk::now_secs(), lifetime)
                {
                    eprintln!("dataplane: disk-cache write failed (advisory): {e}");
                }
                results.push(Vec::new()); // store ack (ignored by the core)
            }

            // Empty output or an unrecognized tag: fall through to the normal serve.
            _ => return None,
        }

        // RESUME: replay the proven core with the grown result list; it returns
        // the next encoded Step.
        let mut resume_in = gw.pool().take();
        frame_resume(prefix, mask, req, &results, &mut resume_in);
        cur = gw.call_seam(resume_in, resume_seam, reply_tx, reply_rx)?;
    }
}

/// First index of `needle` in `hay`.
fn find(hay: &[u8], needle: &[u8]) -> Option<usize> {
    if needle.is_empty() || needle.len() > hay.len() {
        return None;
    }
    hay.windows(needle.len()).position(|w| w == needle)
}

/// The dial/forward timeout — a default.
fn dial_timeout() -> std::time::Duration {
    std::time::Duration::from_millis(500)
}

/// The configured proxy fleet, shared with the established proxy hook (one health
/// loop, one id→socket map). `None` when `DRORB_PROXY_BACKENDS` is unset.
fn fleet() -> Option<&'static std::sync::Arc<Fleet>> {
    crate::proxy_hook::fleet()
}
