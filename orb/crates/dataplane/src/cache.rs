//! Dataplane-side HTTP response cache: the untrusted STORE for the proven
//! core's cacheability decision.
//!
//! The proven serve is a stateless `ByteArray -> ByteArray` transform: it
//! cannot carry a store across calls (`Reactor.Stage.Cache.serveCached` proves
//! the fresh-hit/miss/coalesce semantics over an `RStore`, but the *store* is
//! state the seam has nowhere to keep). So the store lives HERE, on the
//! untrusted host side, and is keyed by the proven core's decision — exactly the
//! sans-IO split the `Cache` library documents: the proven core decides
//! *cacheability, key, and freshness*; the shell only *stores and replays* bytes
//! it was told it may.
//!
//! ## What the proven core decides (this shell does not)
//!
//! * **Key** — method + request-target, the §4.1 exact-key match
//!   (`Cache.Key`/`rkeyOf` reduce to method + target; the deployed serve varies
//!   only on those two here).
//! * **Cacheability + freshness lifetime** — the response carries the directive
//!   the proven core resolved per RFC 9111 §4.2.1 (`Cache.selectLifetime`:
//!   `s-maxage`/`max-age`/`Expires−Date`). This shell reads `Cache-Control:
//!   max-age=N` off the proven response bytes and stores under that lifetime. It
//!   invents no TTL of its own: a response with no such directive is never
//!   stored, so a route is cacheable iff the proven serve says so.
//! * **Fresh-hit replay** — a stored entry is served without re-running the
//!   handler while `current_age < freshness_lifetime` (§4.2), with the age
//!   arithmetic (`current_age = now − stored_at`) the shell measures against the
//!   proven lifetime. `Cache.cache_hit_fresh` is the property this realizes.
//!
//! ## What this shell does (the effect the proven model abstracts)
//!
//! * Holds one process-global map `(method, target) -> (bytes, stored_at,
//!   max_age)` across serve calls.
//! * Stamps `X-Cache: HIT` + `Age: <seconds>` on a replayed response (the
//!   observable a client — and the conformance driver — reads).
//! * **Coalesces** concurrent same-key misses: the first miss is the *leader*
//!   and runs the handler once; every concurrent miss for the same key is a
//!   *waiter* that blocks on the leader's single fetch and is served from it —
//!   K concurrent misses ⇒ ONE handler run, the §4 request-collapsing the
//!   `Cache.coalesce_single_fetch` theorem proves (`locks`/`pending`).
//!
//! The stored value is the genuine proven-serve output, so a replay never
//! diverges from what the handler + response transforms would have produced —
//! the "no mirror" property `serveCached_second_hits` states.

use std::collections::HashMap;
use std::sync::{Arc, Condvar, Mutex, OnceLock};
use std::time::{Duration, Instant};

/// The process-global response cache the effect-seam interpreter threads across
/// serve calls. One store for the whole host, keyed by the PROVEN core decision
/// (the `.cacheLookup` / `.cacheStore` key bytes). The proven serve is a
/// stateless `ByteArray -> ByteArray`; the cross-call state lives here.
pub fn global() -> &'static ResponseCache {
    static CACHE: OnceLock<ResponseCache> = OnceLock::new();
    CACHE.get_or_init(ResponseCache::new)
}

/// A stored response: the proven-serve bytes exactly as produced, the instant it
/// was stored, and the freshness lifetime (seconds) the proven response carried.
struct Entry {
    /// The response bytes as the proven serve produced them (no cache stamp).
    body: Vec<u8>,
    /// When this entry was stored — `current_age = now − stored_at` (§4.2.3).
    stored_at: Instant,
    /// The §4.2.1 freshness lifetime (seconds) resolved by the proven core and
    /// carried on the response as `Cache-Control: max-age`.
    max_age: u64,
}

/// A per-key in-flight fetch other waiters coalesce behind (§4 request
/// collapsing): the leader publishes its single fetch's bytes here and wakes
/// every waiter.
struct InFlight {
    /// `None` until the leader's fetch completes, then the shared response bytes.
    done: Mutex<Option<Arc<Vec<u8>>>>,
    cv: Condvar,
}

/// The dataplane response cache: the store, plus the set of in-flight keys used
/// for coalescing. Both maps are keyed on the proven `(method, target)` decision.
pub struct ResponseCache {
    store: Mutex<HashMap<Vec<u8>, Entry>>,
    inflight: Mutex<HashMap<Vec<u8>, Arc<InFlight>>>,
}

impl Default for ResponseCache {
    fn default() -> Self {
        Self::new()
    }
}

impl ResponseCache {
    pub fn new() -> Self {
        ResponseCache {
            store: Mutex::new(HashMap::new()),
            inflight: Mutex::new(HashMap::new()),
        }
    }

    /// Serve `req` through the cache.
    ///
    /// * A fresh stored entry is replayed (`X-Cache: HIT` + `Age`) WITHOUT
    ///   invoking `fetch` — the handler is not re-run (§4.2 fresh hit).
    /// * A miss runs `fetch` exactly once (the leader); concurrent same-key
    ///   misses coalesce onto that single run (§4 request collapsing) and are
    ///   served from it. If the proven response says it is cacheable (a GET, a
    ///   2xx, and a positive `Cache-Control: max-age`), it is stored under that
    ///   lifetime and the next request within it HITs.
    /// * A request the proven core does not make cacheable (non-GET, or a
    ///   response with no `max-age`) bypasses the store entirely: `fetch` runs
    ///   and its bytes pass through unstamped.
    ///
    /// `fetch` is the proven seam crossing (the real `drorb_serve` /
    /// `drorb_serve_metered`) the host would otherwise call directly.
    pub fn serve<F>(&self, req: &[u8], fetch: F) -> Vec<u8>
    where
        F: FnOnce() -> Vec<u8>,
    {
        // The proven KEY decision: method + target, GET only. A non-GET (or an
        // unparseable head) is never cached — run and pass through.
        let key = match cache_key(req) {
            Some(k) => k,
            None => return fetch(),
        };

        // §4.2 fresh hit: replay the stored bytes, handler NOT run.
        if let Some(hit) = self.try_hit(&key) {
            return hit;
        }

        // Miss: become the leader (run the one fetch) or a waiter (coalesce).
        let (inflight, is_leader) = {
            let mut map = self.inflight.lock().unwrap();
            match map.get(&key) {
                Some(existing) => (existing.clone(), false),
                None => {
                    let f = Arc::new(InFlight {
                        done: Mutex::new(None),
                        cv: Condvar::new(),
                    });
                    map.insert(key.clone(), f.clone());
                    (f, true)
                }
            }
        };

        if !is_leader {
            // Waiter: block on the leader's single fetch, then serve from it.
            // Coalesced followers did not run a handler of their own — they are
            // served from the ONE fetch, marked as a hit (age 0, just fetched).
            let mut done = inflight.done.lock().unwrap();
            while done.is_none() {
                done = inflight.cv.wait(done).unwrap();
            }
            let bytes = done.as_ref().unwrap().clone();
            return stamp(&bytes, b"HIT", Some(0));
        }

        // Leader: run the handler exactly once.
        let resp = fetch();

        // The proven CACHEABILITY decision, read off the response bytes.
        if let Some(max_age) = cacheable_lifetime(&resp) {
            self.store.lock().unwrap().insert(
                key.clone(),
                Entry {
                    body: resp.clone(),
                    stored_at: Instant::now(),
                    max_age,
                },
            );
        }

        // Publish the single fetch to every coalesced waiter, then clear the
        // in-flight marker.
        {
            let shared = Arc::new(resp.clone());
            let mut done = inflight.done.lock().unwrap();
            *done = Some(shared);
            inflight.cv.notify_all();
        }
        self.inflight.lock().unwrap().remove(&key);

        // The leader's own response is a MISS (it just populated the store).
        stamp(&resp, b"MISS", None)
    }

    /// **Effect-seam COALESCING LOOKUP.** Probe the store at the PROVEN key (the
    /// bytes the core's `.cacheLookup` yielded), collapsing concurrent same-key
    /// misses onto ONE fetch (§4 request collapsing):
    ///
    /// * `Some(bytes)` — the request is served WITHOUT running the handler: either
    ///   a fresh store hit, or a coalesced WAITER served the in-flight leader's
    ///   single fetch, in both cases stamped `X-Cache: HIT` + `Age`. The core's
    ///   continuation `.done`s these bytes.
    /// * `None` — this caller is the elected LEADER for a cold key: it runs the
    ///   fold, and its subsequent [`store`](Self::store) publishes the fetched
    ///   bytes to every waiter that collapsed behind it.
    ///
    /// So K concurrent misses on a cold key elect exactly one leader (one fold)
    /// and K−1 waiters served from it — the `Cache.coalesce_single_fetch` property.
    pub fn lookup_coalescing(&self, key: &[u8]) -> Option<Vec<u8>> {
        // §4.2 fresh hit: serve the stored bytes, no coalescing needed.
        if let Some(hit) = self.try_hit(key) {
            return Some(hit);
        }
        // Miss: become the single LEADER for this key, or a WAITER behind it. The
        // election is atomic under the in-flight lock, so exactly one caller leads.
        let (inflight, is_leader) = {
            let mut map = self.inflight.lock().unwrap();
            match map.get(key) {
                Some(existing) => (existing.clone(), false),
                None => {
                    let f = Arc::new(InFlight {
                        done: Mutex::new(None),
                        cv: Condvar::new(),
                    });
                    map.insert(key.to_vec(), f.clone());
                    (f, true)
                }
            }
        };
        if is_leader {
            // The caller runs the fold; `store` publishes the result to waiters.
            return None;
        }
        // Waiter: block on the leader's single fetch, then serve it stamped HIT.
        let mut done = inflight.done.lock().unwrap();
        while done.is_none() {
            let (guard, timeout) = inflight.cv.wait_timeout(done, Duration::from_secs(5)).unwrap();
            done = guard;
            if timeout.timed_out() {
                break;
            }
        }
        match done.as_ref() {
            Some(bytes) => Some(stamp(bytes, b"HIT", Some(0))),
            // The leader never published within the deadline (e.g. serve thread
            // gone): fall back to a fresh store hit, else lead the fold ourselves.
            None => self.try_hit(key),
        }
    }

    /// **Effect-seam STORE.** Store `resp` under the PROVEN `key` with the PROVEN
    /// `lifetime` (seconds) the core's `.cacheStore` yielded — the core decided
    /// cacheability, key, and lifetime; this shell only holds the bytes. A
    /// non-positive lifetime is not stored (nothing cacheable to hold). In every
    /// case the single fetch is published to any waiters that coalesced behind
    /// this leader (via [`lookup_coalescing`](Self::lookup_coalescing)) and the
    /// in-flight marker is cleared.
    pub fn store(&self, key: &[u8], resp: &[u8], lifetime: u64) {
        if lifetime != 0 {
            self.store.lock().unwrap().insert(
                key.to_vec(),
                Entry {
                    body: resp.to_vec(),
                    stored_at: Instant::now(),
                    max_age: lifetime,
                },
            );
        }
        // Publish this single fetch to every coalesced waiter and clear the
        // in-flight marker (the store insert above is already visible, so a late
        // arrival either hits the store or waits on — and is woken by — this).
        if let Some(f) = self.inflight.lock().unwrap().remove(key) {
            let mut done = f.done.lock().unwrap();
            if done.is_none() {
                *done = Some(Arc::new(resp.to_vec()));
            }
            f.cv.notify_all();
        }
    }

    /// A fresh store hit for `key`, replayed with `X-Cache: HIT` + `Age`, or
    /// `None` on a miss / a stale entry (which is evicted).
    fn try_hit(&self, key: &[u8]) -> Option<Vec<u8>> {
        let mut store = self.store.lock().unwrap();
        let entry = store.get(key)?;
        let age = entry.stored_at.elapsed().as_secs();
        if age < entry.max_age {
            // §4.2: response_is_fresh — serve the stored bytes, no handler.
            Some(stamp(&entry.body, b"HIT", Some(age)))
        } else {
            // Stale: drop it so the next request repopulates (no ad-hoc serve).
            store.remove(key);
            None
        }
    }

    /// Test/inspection: number of stored entries.
    #[cfg(test)]
    fn len(&self) -> usize {
        self.store.lock().unwrap().len()
    }
}

/// The proven KEY: `method + b' ' + request-target`, GET only. Returns `None`
/// for a non-GET request or an unparseable request line — neither is cached.
fn cache_key(req: &[u8]) -> Option<Vec<u8>> {
    let line_end = find(req, b"\r\n")?;
    let line = &req[..line_end];
    let mut parts = line.split(|&b| b == b' ');
    let method = parts.next()?;
    let target = parts.next()?;
    if method != b"GET" {
        return None;
    }
    let mut key = Vec::with_capacity(method.len() + 1 + target.len());
    key.extend_from_slice(method);
    key.push(b' ');
    key.extend_from_slice(target);
    Some(key)
}

/// The proven CACHEABILITY decision, read off the response bytes: `Some(max_age)`
/// iff the response is a 2xx carrying a positive `Cache-Control: max-age=N` (the
/// §4.2.1 freshness lifetime the proven core resolved). `None` — do not store.
fn cacheable_lifetime(resp: &[u8]) -> Option<u64> {
    // Status must be 2xx (a cacheable status for the routes modeled here).
    if !status_is_2xx(resp) {
        return None;
    }
    let head_end = find(resp, b"\r\n\r\n").map(|p| p + 2).unwrap_or(resp.len());
    let head = &resp[..head_end];
    let max_age = parse_max_age(head)?;
    if max_age == 0 {
        return None;
    }
    Some(max_age)
}

/// `true` iff the status line is `HTTP/x.y 2NN`.
fn status_is_2xx(resp: &[u8]) -> bool {
    let line_end = find(resp, b"\r\n").unwrap_or(resp.len());
    let line = &resp[..line_end];
    // `HTTP/1.1 200 OK` — the code is the second space-separated field.
    let mut parts = line.split(|&b| b == b' ');
    let _ver = parts.next();
    match parts.next() {
        Some(code) => code.first() == Some(&b'2') && code.len() == 3,
        None => false,
    }
}

/// Scan a response head for `Cache-Control: max-age=N` (case-insensitive header
/// name) and return `N`. `None` if absent or unparseable.
fn parse_max_age(head: &[u8]) -> Option<u64> {
    for line in head.split(|&b| b == b'\n') {
        let line = line.strip_suffix(b"\r").unwrap_or(line);
        let colon = match line.iter().position(|&b| b == b':') {
            Some(c) => c,
            None => continue, // the status line and any fold have no name:value
        };
        let (name, rest) = line.split_at(colon);
        if !name.eq_ignore_ascii_case(b"cache-control") {
            continue;
        }
        let value = &rest[1..]; // drop the ':'
        // Find the `max-age=` directive (case-insensitive) among comma-separated
        // directives; take the digits after '='.
        for directive in value.split(|&b| b == b',') {
            let directive = trim(directive);
            let eq = match directive.iter().position(|&b| b == b'=') {
                Some(e) => e,
                None => continue,
            };
            let (dname, dval) = directive.split_at(eq);
            if !trim(dname).eq_ignore_ascii_case(b"max-age") {
                continue;
            }
            let digits = trim(&dval[1..]); // drop the '='
            let s = std::str::from_utf8(digits).ok()?;
            return s.parse::<u64>().ok();
        }
    }
    None
}

/// Stamp `X-Cache` (and optionally `Age`) onto a response, inserted right after
/// the status line so the body and every existing header are preserved
/// byte-for-byte (Content-Length still describes the unchanged body).
fn stamp(resp: &[u8], xcache: &[u8], age: Option<u64>) -> Vec<u8> {
    let insert_at = match find(resp, b"\r\n") {
        Some(p) => p + 2,
        None => return resp.to_vec(), // no status line: nothing to stamp
    };
    let mut out = Vec::with_capacity(resp.len() + 40);
    out.extend_from_slice(&resp[..insert_at]);
    out.extend_from_slice(b"X-Cache: ");
    out.extend_from_slice(xcache);
    out.extend_from_slice(b"\r\n");
    if let Some(a) = age {
        out.extend_from_slice(format!("Age: {a}\r\n").as_bytes());
    }
    out.extend_from_slice(&resp[insert_at..]);
    out
}

/// First index of `needle` in `hay`.
fn find(hay: &[u8], needle: &[u8]) -> Option<usize> {
    if needle.is_empty() || needle.len() > hay.len() {
        return None;
    }
    hay.windows(needle.len()).position(|w| w == needle)
}

/// Trim ASCII whitespace from both ends.
fn trim(b: &[u8]) -> &[u8] {
    let s = b.iter().position(|c| !c.is_ascii_whitespace()).unwrap_or(b.len());
    let e = b
        .iter()
        .rposition(|c| !c.is_ascii_whitespace())
        .map(|p| p + 1)
        .unwrap_or(s);
    &b[s..e]
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::{Arc, Barrier};
    use std::time::Duration;

    // A cacheable proven-serve response: 200 with `Cache-Control: max-age=60`.
    fn cacheable_resp(body: &str) -> Vec<u8> {
        format!(
            "HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\nCache-Control: max-age=60\r\nContent-Length: {}\r\n\r\n{}",
            body.len(),
            body
        )
        .into_bytes()
    }

    fn get(path: &str) -> Vec<u8> {
        format!("GET {path} HTTP/1.1\r\nHost: x\r\n\r\n").into_bytes()
    }

    fn header_present(resp: &[u8], name: &str) -> bool {
        let head_end = find(resp, b"\r\n\r\n").map(|p| p + 2).unwrap_or(resp.len());
        String::from_utf8_lossy(&resp[..head_end])
            .to_lowercase()
            .contains(&name.to_lowercase())
    }

    #[test]
    fn cache_hit_second_request_from_store() {
        let cache = ResponseCache::new();
        let runs = AtomicUsize::new(0);
        let req = get("/cached");

        // First request: MISS — the handler runs and the response is stored.
        let first = cache.serve(&req, || {
            runs.fetch_add(1, Ordering::SeqCst);
            cacheable_resp("cached-body")
        });
        assert_eq!(runs.load(Ordering::SeqCst), 1, "first request runs the handler");
        assert!(header_present(&first, "x-cache: miss"), "first is a MISS");

        // Let real time pass so the Age arithmetic (now − stored_at) is visibly
        // non-zero — the age is measured, not hardcoded.
        std::thread::sleep(Duration::from_millis(1100));

        // Second identical request: HIT — the handler MUST NOT run again.
        let second = cache.serve(&req, || {
            runs.fetch_add(1, Ordering::SeqCst);
            panic!("handler re-run on a cache HIT");
        });
        assert_eq!(runs.load(Ordering::SeqCst), 1, "handler not re-run on a HIT");
        assert!(header_present(&second, "x-cache: hit"), "second is a HIT");
        assert!(header_present(&second, "age: 1"), "HIT carries a computed Age");
        // The replayed body is byte-identical to the stored serve output.
        assert!(
            String::from_utf8_lossy(&second).ends_with("cached-body"),
            "replay is byte-identical"
        );

        println!("\n--- cache-hit: 2nd response served from the store ---");
        println!("{}", String::from_utf8_lossy(&second));
        println!("handler runs total: {}", runs.load(Ordering::SeqCst));
    }

    #[test]
    fn non_get_is_never_cached() {
        let cache = ResponseCache::new();
        let runs = AtomicUsize::new(0);
        let req = b"POST /cached HTTP/1.1\r\nHost: x\r\n\r\n".to_vec();
        for _ in 0..2 {
            let _ = cache.serve(&req, || {
                runs.fetch_add(1, Ordering::SeqCst);
                cacheable_resp("x")
            });
        }
        assert_eq!(runs.load(Ordering::SeqCst), 2, "POST always runs the handler");
        assert_eq!(cache.len(), 0, "non-GET never stored");
    }

    #[test]
    fn no_cache_control_is_not_stored() {
        let cache = ResponseCache::new();
        let runs = AtomicUsize::new(0);
        let req = get("/health");
        let plain = b"HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nok".to_vec();
        for _ in 0..2 {
            let _ = cache.serve(&req, || {
                runs.fetch_add(1, Ordering::SeqCst);
                plain.clone()
            });
        }
        assert_eq!(
            runs.load(Ordering::SeqCst),
            2,
            "a response with no max-age is never cacheable — handler runs every time"
        );
        assert_eq!(cache.len(), 0);
    }

    #[test]
    fn coalesce_k_concurrent_misses_one_fetch() {
        let cache = Arc::new(ResponseCache::new());
        let runs = Arc::new(AtomicUsize::new(0));
        const K: usize = 8;
        let barrier = Arc::new(Barrier::new(K));
        let req = get("/cached");

        let handles: Vec<_> = (0..K)
            .map(|_| {
                let cache = cache.clone();
                let runs = runs.clone();
                let barrier = barrier.clone();
                let req = req.clone();
                std::thread::spawn(move || {
                    barrier.wait(); // all K arrive together, cold cache
                    cache.serve(&req, || {
                        runs.fetch_add(1, Ordering::SeqCst);
                        std::thread::sleep(Duration::from_millis(150));
                        cacheable_resp("coalesced")
                    })
                })
            })
            .collect();

        let mut hit_or_miss = 0usize;
        for h in handles {
            let resp = h.join().unwrap();
            if header_present(&resp, "x-cache") {
                hit_or_miss += 1;
            }
            assert!(
                String::from_utf8_lossy(&resp).ends_with("coalesced"),
                "every coalesced request gets the ONE fetch's body"
            );
        }
        let total = runs.load(Ordering::SeqCst);
        assert_eq!(total, 1, "K={K} concurrent same-key misses ⇒ exactly ONE fetch");
        assert_eq!(hit_or_miss, K, "all K served");
        println!("\n--- cache-coalesce: {K} concurrent same-key misses ---");
        println!("handler fetches: {total} (expected 1)");
    }

    #[test]
    fn comp_cache_gzip_replays_compressed_body() {
        // A cached, gzip-compressed response: the second request returns the
        // cached compressed body (Content-Encoding: gzip) without the handler.
        let cache = ResponseCache::new();
        let runs = AtomicUsize::new(0);
        let req = get("/cached");
        let gz_body = [0x1f, 0x8b, 0x08, 0x00, 0xde, 0xad, 0xbe, 0xef]; // gzip magic + bytes
        let resp = {
            let mut r = format!(
                "HTTP/1.1 200 OK\r\nContent-Encoding: gzip\r\nCache-Control: max-age=60\r\nContent-Length: {}\r\n\r\n",
                gz_body.len()
            )
            .into_bytes();
            r.extend_from_slice(&gz_body);
            r
        };

        let first = cache.serve(&req, || {
            runs.fetch_add(1, Ordering::SeqCst);
            resp.clone()
        });
        assert!(header_present(&first, "content-encoding: gzip"));

        let second = cache.serve(&req, || {
            runs.fetch_add(1, Ordering::SeqCst);
            panic!("handler re-run on a cached gzip HIT");
        });
        assert_eq!(runs.load(Ordering::SeqCst), 1, "gzip body served from cache");
        assert!(header_present(&second, "x-cache: hit"));
        assert!(header_present(&second, "content-encoding: gzip"));
        // The compressed body bytes survive the replay byte-for-byte.
        assert!(
            second.ends_with(&gz_body),
            "the cached compressed body is replayed unchanged"
        );
        println!("\n--- comp-cache-gzip: cached compressed body replayed on HIT ---");
        println!("handler runs total: {}", runs.load(Ordering::SeqCst));
    }

    #[test]
    fn parse_max_age_variants() {
        assert_eq!(parse_max_age(b"Cache-Control: max-age=60\r\n"), Some(60));
        assert_eq!(
            parse_max_age(b"cache-control: public, max-age=120, s-maxage=30\r\n"),
            Some(120)
        );
        assert_eq!(parse_max_age(b"Cache-Control: no-store\r\n"), None);
        assert_eq!(parse_max_age(b"Content-Type: text/plain\r\n"), None);
    }

    #[test]
    fn stale_entry_evicted_and_refetched() {
        let cache = ResponseCache::new();
        let runs = AtomicUsize::new(0);
        let req = get("/cached");
        // max-age=0 is not cacheable at all; use a tiny lifetime by hand.
        let resp = b"HTTP/1.1 200 OK\r\nCache-Control: max-age=1\r\nContent-Length: 1\r\n\r\nx".to_vec();
        let _ = cache.serve(&req, || {
            runs.fetch_add(1, Ordering::SeqCst);
            resp.clone()
        });
        assert_eq!(cache.len(), 1);
        // Force the stored entry stale by back-dating it beyond its lifetime.
        {
            let key = cache_key(&req).unwrap();
            let mut store = cache.store.lock().unwrap();
            if let Some(e) = store.get_mut(&key) {
                e.stored_at = Instant::now() - Duration::from_secs(5);
            }
        }
        // Next request: stale ⇒ evicted ⇒ handler runs again.
        let _ = cache.serve(&req, || {
            runs.fetch_add(1, Ordering::SeqCst);
            resp.clone()
        });
        assert_eq!(runs.load(Ordering::SeqCst), 2, "stale entry refetched");
    }
}
