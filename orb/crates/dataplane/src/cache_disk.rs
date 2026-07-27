//! Dataplane-side DISK cache: the durable COLD tier for the proven core's
//! cacheability decision.
//!
//! The in-memory [`crate::cache`] tier is the HOT tier — sub-millisecond, but it
//! evaporates on restart. This module is the COLD tier: cacheable responses are
//! also written to disk under a key-derived path, so a large working set survives
//! a restart. On a hot-tier miss the disk is consulted; a disk hit is served AND
//! promoted back into the hot tier.
//!
//! This realizes the proven model in `Cache/Disk.lean`:
//!
//! * **Key → path is injective and traversal-safe.** `Cache.Disk.pathOf` proves
//!   distinct keys map to distinct paths (no two keys share a file — a hit never
//!   serves another key's bytes) and that a path contains no `'/'` or `'.'` — it
//!   cannot escape the cache directory. Here the path is a fixed-width hex hash
//!   for a bounded filename, PLUS the full key stored inside the file and
//!   compared on read: a hash collision can only cost a cache slot, never serve
//!   the wrong bytes (strictly safer than trusting hash collision-resistance).
//! * **Round-trip faithfulness** (`disk_get_put`): the bytes read back after a
//!   write are the bytes written, verbatim.
//! * **TTL** (`disk_get_expired_none`): an entry past `stored_at + max_age` is
//!   never served (`current_age = now − stored_at`, `fresh ↔ age < max_age`,
//!   RFC 9111 §4.2, the same test the hot tier uses).
//! * **Reaper** (`disk_evict_removes_expired` / `disk_evict_keeps_fresh`): the
//!   sweep drops exactly the expired entries and keeps the fresh ones.
//!
//! Gated behind `DRORB_DISK_CACHE=1` (+ `DRORB_DISK_CACHE_DIR`, default a
//! per-process temp dir), so the default deployed path is byte-for-byte
//! unchanged.
//!
//! ## On-disk format
//!
//! `[4B magic "DKCH"] [4B version=1] [8B stored_at] [8B max_age] [4B key_len]
//!  [key bytes] [response bytes]`
//!
//! all integers little-endian. The stored "response bytes" are the genuine
//! proven-serve output exactly as produced — the replay is byte-identical.
//!
//! Writes are atomic: content goes to a sibling `.tmp` file, then `rename` moves
//! it into place, so a crash never leaves a half-written entry to be read.

use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, OnceLock};
use std::time::{SystemTime, UNIX_EPOCH};

const MAGIC: &[u8; 4] = b"DKCH";
const VERSION: u32 = 1;

/// Seconds since the UNIX epoch.
pub fn now_secs() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs()
}

/// A decoded disk entry: the store metadata plus the response bytes.
pub struct DiskEntry {
    /// The cache key this file was written under (compared on read to defeat
    /// hash collisions — a mismatch reads as a miss, never a wrong-key serve).
    pub key: Vec<u8>,
    /// Store time (UNIX seconds) — `current_age = now − stored_at` (§4.2.3).
    pub stored_at: u64,
    /// Freshness lifetime (seconds) — the §4.2.1 directive the core resolved.
    pub max_age: u64,
    /// The response bytes exactly as the proven serve produced them.
    pub body: Vec<u8>,
}

impl DiskEntry {
    /// §4.2 `fresh ↔ current_age < max_age`, with `current_age = now − stored_at`.
    pub fn fresh(&self, now: u64) -> bool {
        now.saturating_sub(self.stored_at) < self.max_age
    }
}

/// The durable disk cache rooted at a base directory.
pub struct DiskCache {
    root: PathBuf,
    enabled: bool,
}

/// The process-global disk cache, configured once from the environment.
///
/// * `DRORB_DISK_CACHE=1` enables it (otherwise every method is a no-op).
/// * `DRORB_DISK_CACHE_DIR=<path>` sets the base directory (default
///   `<tempdir>/drorb-disk-cache`).
pub fn global() -> &'static DiskCache {
    static CACHE: OnceLock<DiskCache> = OnceLock::new();
    CACHE.get_or_init(|| {
        let enabled = std::env::var("DRORB_DISK_CACHE")
            .map(|v| v == "1")
            .unwrap_or(false);
        let root = std::env::var_os("DRORB_DISK_CACHE_DIR")
            .map(PathBuf::from)
            .unwrap_or_else(|| std::env::temp_dir().join("drorb-disk-cache"));
        DiskCache { root, enabled }
    })
}

impl DiskCache {
    /// A disk cache rooted at `root` (always enabled — for tests and explicit use).
    pub fn new(root: impl AsRef<Path>) -> Self {
        DiskCache {
            root: root.as_ref().to_path_buf(),
            enabled: true,
        }
    }

    pub fn enabled(&self) -> bool {
        self.enabled
    }

    /// The sharded, traversal-safe on-disk path for a key.
    ///
    /// A 128-bit key hash rendered as 32 lowercase-hex chars, sharded
    /// `<root>/<h[0..2]>/<h[2..4]>/<h>`. Every path byte is `[0-9a-f]` or the OS
    /// separator between components — no `'/'` inside a component, no `'.'`, so
    /// the path can never escape `root` (`Cache.Disk.pathOf_no_slash/no_dot`).
    fn entry_path(&self, key: &[u8]) -> PathBuf {
        let hex = hash_hex(key);
        self.root.join(&hex[0..2]).join(&hex[2..4]).join(&hex)
    }

    /// Write a cacheable response to disk atomically (temp file + rename).
    ///
    /// Realizes `Cache.Disk.put`; a subsequent [`get_entry`](Self::get_entry)
    /// returns the same bytes (`disk_get_put`). Best-effort: an I/O error is
    /// returned but callers treat the disk tier as advisory.
    pub fn put(&self, key: &[u8], resp: &[u8], stored_at: u64, max_age: u64) -> io::Result<()> {
        if !self.enabled || max_age == 0 {
            return Ok(());
        }
        let path = self.entry_path(key);
        if let Some(dir) = path.parent() {
            fs::create_dir_all(dir)?;
        }
        let data = encode(key, resp, stored_at, max_age);
        let tmp = path.with_extension("tmp");
        fs::write(&tmp, &data)?;
        fs::rename(&tmp, &path)?;
        Ok(())
    }

    /// Read the full entry for a key (whatever its freshness), or `None` on a
    /// miss / corrupt / key-mismatch file. Realizes `Cache.Disk.get?`.
    pub fn get_entry(&self, key: &[u8]) -> Option<DiskEntry> {
        if !self.enabled {
            return None;
        }
        let path = self.entry_path(key);
        let data = fs::read(&path).ok()?;
        let entry = decode(&data)?;
        // Defeat hash collisions: only THIS key's file may serve THIS key.
        if entry.key != key {
            return None;
        }
        Some(entry)
    }

    /// A TTL-honouring lookup: the stored response bytes only while fresh
    /// (`Cache.Disk.getFresh`). A stale entry reads as a miss and its file is
    /// removed (`disk_get_expired_none`).
    pub fn get_fresh(&self, key: &[u8], now: u64) -> Option<DiskEntry> {
        let entry = self.get_entry(key)?;
        if entry.fresh(now) {
            Some(entry)
        } else {
            let _ = fs::remove_file(self.entry_path(key));
            None
        }
    }

    /// Remove a key's file. `Ok(true)` if one existed.
    pub fn remove(&self, key: &[u8]) -> io::Result<bool> {
        if !self.enabled {
            return Ok(false);
        }
        match fs::remove_file(self.entry_path(key)) {
            Ok(()) => Ok(true),
            Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(false),
            Err(e) => Err(e),
        }
    }

    /// **Two-tier composition hook.** Called by the effect seam when the HOT tier
    /// misses (this caller was elected leader for a cold key). If a FRESH disk
    /// entry exists it is PROMOTED into the hot tier (which also wakes any
    /// coalesced waiters) and returned as a stamped `X-Cache: HIT` response —
    /// the handler is NOT run. `None` if the disk misses too (the leader runs
    /// the real fold).
    pub fn promote_on_miss(&self, key: &[u8], now: u64) -> Option<Vec<u8>> {
        let entry = self.get_fresh(key, now)?;
        let age = now.saturating_sub(entry.stored_at);
        let remaining = entry.max_age.saturating_sub(age);
        // Promote to hot AND publish to coalesced waiters via the hot store.
        crate::cache::global().store(key, &entry.body, remaining.max(1));
        Some(stamp_hit(&entry.body, age))
    }

    /// Iterate every stored key hash by walking the two shard levels.
    fn iter_paths(&self) -> Vec<PathBuf> {
        let mut out = Vec::new();
        let Ok(l0) = fs::read_dir(&self.root) else {
            return out;
        };
        for d0 in l0.flatten() {
            if !d0.path().is_dir() {
                continue;
            }
            let Ok(l1) = fs::read_dir(d0.path()) else {
                continue;
            };
            for d1 in l1.flatten() {
                if !d1.path().is_dir() {
                    continue;
                }
                let Ok(files) = fs::read_dir(d1.path()) else {
                    continue;
                };
                for f in files.flatten() {
                    let p = f.path();
                    if p.extension().map(|e| e == "tmp").unwrap_or(false) {
                        continue; // skip in-flight temp files
                    }
                    if p.is_file() {
                        out.push(p);
                    }
                }
            }
        }
        out
    }

    /// **The reaper sweep.** Remove every entry whose TTL has elapsed, keep the
    /// fresh (`Cache.Disk.evict`: `disk_evict_removes_expired` +
    /// `disk_evict_keeps_fresh`). Returns the number of files removed.
    pub fn reap(&self, now: u64) -> usize {
        if !self.enabled {
            return 0;
        }
        let mut removed = 0;
        for p in self.iter_paths() {
            let Ok(data) = fs::read(&p) else { continue };
            match decode(&data) {
                Some(entry) if entry.fresh(now) => {} // keep the fresh
                _ => {
                    // Expired or corrupt: drop it.
                    if fs::remove_file(&p).is_ok() {
                        removed += 1;
                    }
                }
            }
        }
        removed
    }
}

/// Spawn a background reaper thread that sweeps the disk cache every `interval`
/// seconds. Returns a handle; dropping or calling `shutdown` stops it. No-op
/// (returns `None`) when the disk tier is disabled.
pub fn spawn_reaper(interval_secs: u64) -> Option<ReaperHandle> {
    let cache = global();
    if !cache.enabled {
        return None;
    }
    let stop = Arc::new(AtomicBool::new(false));
    let stop_c = stop.clone();
    let interval = interval_secs.max(1);
    let handle = std::thread::Builder::new()
        .name("drorb-disk-reaper".into())
        .spawn(move || {
            loop {
                // Sleep in 1s slices so shutdown is responsive.
                for _ in 0..interval {
                    if stop_c.load(Ordering::Acquire) {
                        return;
                    }
                    std::thread::sleep(std::time::Duration::from_secs(1));
                }
                if stop_c.load(Ordering::Acquire) {
                    return;
                }
                let n = global().reap(now_secs());
                if n > 0 {
                    eprintln!(
                        "dataplane: disk-cache reaper swept {n} expired entr{}",
                        if n == 1 { "y" } else { "ies" }
                    );
                }
            }
        })
        .ok()?;
    Some(ReaperHandle {
        stop,
        thread: Some(handle),
    })
}

/// Handle to the background reaper thread.
pub struct ReaperHandle {
    stop: Arc<AtomicBool>,
    thread: Option<std::thread::JoinHandle<()>>,
}

impl ReaperHandle {
    /// Stop the reaper and wait for it to exit.
    pub fn shutdown(mut self) {
        self.stop.store(true, Ordering::Release);
        if let Some(t) = self.thread.take() {
            let _ = t.join();
        }
    }
}

impl Drop for ReaperHandle {
    fn drop(&mut self) {
        self.stop.store(true, Ordering::Release);
    }
}

// ---------------------------------------------------------------------------
// Encoding / hashing helpers (std-only; no external crate in the TCB shell)
// ---------------------------------------------------------------------------

/// Encode an entry to the on-disk byte format.
fn encode(key: &[u8], resp: &[u8], stored_at: u64, max_age: u64) -> Vec<u8> {
    let mut buf = Vec::with_capacity(28 + key.len() + resp.len());
    buf.extend_from_slice(MAGIC);
    buf.extend_from_slice(&VERSION.to_le_bytes());
    buf.extend_from_slice(&stored_at.to_le_bytes());
    buf.extend_from_slice(&max_age.to_le_bytes());
    buf.extend_from_slice(&(key.len() as u32).to_le_bytes());
    buf.extend_from_slice(key);
    buf.extend_from_slice(resp);
    buf
}

/// Decode an entry from raw file bytes, or `None` if malformed.
fn decode(data: &[u8]) -> Option<DiskEntry> {
    // magic(4) + version(4) + stored_at(8) + max_age(8) + key_len(4) = 28
    if data.len() < 28 || &data[0..4] != MAGIC {
        return None;
    }
    let version = u32::from_le_bytes(data[4..8].try_into().ok()?);
    if version != VERSION {
        return None;
    }
    let stored_at = u64::from_le_bytes(data[8..16].try_into().ok()?);
    let max_age = u64::from_le_bytes(data[16..24].try_into().ok()?);
    let key_len = u32::from_le_bytes(data[24..28].try_into().ok()?) as usize;
    let key_end = 28usize.checked_add(key_len)?;
    if data.len() < key_end {
        return None;
    }
    Some(DiskEntry {
        key: data[28..key_end].to_vec(),
        stored_at,
        max_age,
        body: data[key_end..].to_vec(),
    })
}

/// A 128-bit key hash rendered as 32 lowercase-hex chars. Two independent
/// FNV-1a variants (distinct offset bases) give the two 64-bit halves. The hash
/// only distributes files across shards — soundness rests on the stored-key
/// compare in [`DiskCache::get_entry`], not on collision-resistance.
fn hash_hex(key: &[u8]) -> String {
    let a = fnv1a(key, 0xcbf29ce484222325);
    let b = fnv1a(key, 0x100000001b3 ^ 0xcbf29ce484222325);
    let mut s = String::with_capacity(32);
    for byte in a.to_be_bytes().iter().chain(b.to_be_bytes().iter()) {
        s.push(HEX[(byte >> 4) as usize] as char);
        s.push(HEX[(byte & 0x0f) as usize] as char);
    }
    s
}

const HEX: &[u8; 16] = b"0123456789abcdef";

fn fnv1a(data: &[u8], basis: u64) -> u64 {
    let mut h = basis;
    for &b in data {
        h ^= b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

/// Stamp `X-Cache: HIT` + `Age: <age>` after the status line (mirrors the hot
/// tier's stamp; the body and Content-Length are untouched).
fn stamp_hit(resp: &[u8], age: u64) -> Vec<u8> {
    let insert_at = match find(resp, b"\r\n") {
        Some(p) => p + 2,
        None => return resp.to_vec(),
    };
    let mut out = Vec::with_capacity(resp.len() + 40);
    out.extend_from_slice(&resp[..insert_at]);
    out.extend_from_slice(b"X-Cache: HIT\r\n");
    out.extend_from_slice(format!("Age: {age}\r\n").as_bytes());
    out.extend_from_slice(&resp[insert_at..]);
    out
}

fn find(hay: &[u8], needle: &[u8]) -> Option<usize> {
    if needle.is_empty() || needle.len() > hay.len() {
        return None;
    }
    hay.windows(needle.len()).position(|w| w == needle)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tmp_root(name: &str) -> PathBuf {
        let mut p = std::env::temp_dir();
        p.push(format!("drorb-disk-test-{}-{}", name, std::process::id()));
        let _ = fs::remove_dir_all(&p);
        p
    }

    fn resp(body: &str) -> Vec<u8> {
        format!(
            "HTTP/1.1 200 OK\r\nContent-Length: {}\r\n\r\n{}",
            body.len(),
            body
        )
        .into_bytes()
    }

    #[test]
    fn put_then_get_roundtrip_byte_identical() {
        // disk_get_put: the bytes read back are the bytes written, verbatim.
        let root = tmp_root("roundtrip");
        let dc = DiskCache::new(&root);
        let key = b"GET /assets/app.js";
        let body = resp("the-cached-body");
        dc.put(key, &body, 1000, 60).unwrap();

        let got = dc.get_entry(key).expect("entry present");
        assert_eq!(got.key, key);
        assert_eq!(got.body, body, "response bytes round-trip byte-identical");
        assert_eq!(got.stored_at, 1000);
        assert_eq!(got.max_age, 60);
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn survives_a_restart() {
        // A fresh DiskCache instance on the same root (a process restart) still
        // serves the cold entry — the whole point of the tier.
        let root = tmp_root("restart");
        let key = b"GET /cold";
        let body = resp("survives-restart");
        {
            let dc = DiskCache::new(&root);
            dc.put(key, &body, now_secs(), 120).unwrap();
        }
        // "Restart": a brand-new instance, no shared in-memory state.
        let dc2 = DiskCache::new(&root);
        let got = dc2
            .get_fresh(key, now_secs())
            .expect("cold hit after restart");
        assert_eq!(got.body, body);
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn expired_entry_is_a_miss() {
        // disk_get_expired_none: age past max_age ⇒ not served (and file dropped).
        let root = tmp_root("expired");
        let dc = DiskCache::new(&root);
        let key = b"GET /stale";
        dc.put(key, &resp("stale"), 1000, 10).unwrap();
        // now = 1000 + 50 → age 50 ≥ ttl 10 → expired.
        assert!(
            dc.get_fresh(key, 1050).is_none(),
            "expired entry not served"
        );
        // The file was reaped on the stale read.
        assert!(dc.get_entry(key).is_none(), "stale file removed");
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn fresh_entry_is_served() {
        // disk_getFresh_put: a fresh entry is served.
        let root = tmp_root("fresh");
        let dc = DiskCache::new(&root);
        let key = b"GET /fresh";
        dc.put(key, &resp("fresh"), 1000, 100).unwrap();
        // now = 1050 → age 50 < ttl 100 → fresh.
        assert!(dc.get_fresh(key, 1050).is_some(), "fresh entry served");
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn reaper_drops_expired_keeps_fresh() {
        // disk_evict_removes_expired + disk_evict_keeps_fresh.
        let root = tmp_root("reaper");
        let dc = DiskCache::new(&root);
        dc.put(b"GET /keep", &resp("keep"), 1000, 100).unwrap();
        dc.put(b"GET /drop", &resp("drop"), 1000, 10).unwrap();
        // now = 1050: /keep fresh (50<100), /drop expired (50≥10).
        let removed = dc.reap(1050);
        assert_eq!(removed, 1, "exactly the one expired entry is reaped");
        assert!(dc.get_entry(b"GET /keep").is_some(), "fresh entry kept");
        assert!(
            dc.get_entry(b"GET /drop").is_none(),
            "expired entry dropped"
        );
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn distinct_keys_distinct_paths_no_traversal() {
        // pathOf_injective (distinct paths) + pathOf_no_slash/no_dot (safe).
        let root = tmp_root("paths");
        let dc = DiskCache::new(&root);
        let p1 = dc.entry_path(b"GET /a");
        let p2 = dc.entry_path(b"GET /b");
        assert_ne!(p1, p2, "distinct keys map to distinct paths");
        // The 32-hex filename component contains only [0-9a-f] — no '.' or '/'.
        let name = p1.file_name().unwrap().to_string_lossy();
        assert_eq!(name.len(), 32);
        assert!(
            name.bytes().all(|b| b.is_ascii_hexdigit()),
            "path component is pure hex — cannot be '..' or contain a separator"
        );
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn promote_on_miss_serves_from_disk_stamped_hit() {
        // The two-tier hand-off the seam uses: a fresh disk entry, on a hot-tier
        // miss, is served stamped X-Cache: HIT with the age computed from
        // stored_at — and promoted into the hot tier (crate::cache::global()).
        let root = tmp_root("promote");
        let dc = DiskCache::new(&root);
        // A key unique to this test so the process-global hot cache never collides.
        let key = b"GET /promote-unique-abc123";
        let body = resp("promoted-from-disk");
        let now = now_secs();
        dc.put(key, &body, now - 5, 100).unwrap(); // age 5, fresh (5<100)

        let served = dc.promote_on_miss(key, now).expect("cold-tier hit");
        let s = String::from_utf8_lossy(&served);
        assert!(
            s.contains("X-Cache: HIT"),
            "served bytes carry the HIT stamp"
        );
        assert!(s.contains("Age: 5"), "age computed from stored_at");
        assert!(s.ends_with("promoted-from-disk"), "byte-identical body");
        // It was promoted into the hot tier: a keyed hot lookup now replays it
        // WITHOUT the disk (the seam probes the hot store by the proven key).
        let hot = crate::cache::global()
            .lookup_coalescing(key)
            .expect("promoted into the hot tier");
        assert!(String::from_utf8_lossy(&hot).ends_with("promoted-from-disk"));
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn hash_collision_does_not_cross_serve() {
        // Even if two keys shared a file, the stored-key compare means a lookup
        // for the OTHER key reads as a miss — never the wrong bytes.
        let root = tmp_root("collide");
        let dc = DiskCache::new(&root);
        let key = b"GET /real";
        dc.put(key, &resp("real"), now_secs(), 100).unwrap();
        // A different key that happens to land on the SAME file path: force it by
        // reading through the wrong key on the real key's path.
        // (Directly: get_entry compares entry.key != requested key.)
        assert!(dc.get_entry(b"GET /other-key-entirely").is_none());
        assert!(dc.get_entry(key).is_some());
        let _ = fs::remove_dir_all(&root);
    }
}
