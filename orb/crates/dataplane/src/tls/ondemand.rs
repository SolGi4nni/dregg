//! On-demand TLS: mint a certificate per-SNI on the first handshake that asks
//! for a host we do not already hold a leaf for — the `*.apps.example.test` pattern.
//!
//! ## Where this sits, and what stays verified
//!
//! The TLS handshake itself — ClientHello parse (including SNI), `chooseCert`,
//! the whole RFC 8446 flight — runs INSIDE the proven Lean server
//! (`drorb_tls_serve`), over a certificate POOL handed in per connection. This
//! module is the untrusted SHELL that decides WHICH pool a fresh SNI gets:
//!
//!   1. the accept loop PEEKS the ClientHello (`MSG_PEEK`, non-destructive) and
//!      reads the SNI — a *provisioning hint only*; the proven parser re-reads
//!      the SNI authoritatively from the same bytes and `chooseCert` selects the
//!      leaf. A wrong peek can only mis-provision (the handshake then fails
//!      cleanly); it can never cause a mis-issued or mis-presented certificate;
//!   2. for an SNI we hold no cert for, we ASK the operator's authorizer
//!      (`GET http://<ask>/internal/site-exists?domain=<sni>`); a refusal drops
//!      the handshake;
//!   3. an allowed SNI is MINTED by the verified ACME driver (`acme-issue`, the
//!      RFC 8555 flow over drorb's own verified TLS client + audited HACL*/
//!      EverCrypt primitives — this module only spawns it), which lands an
//!      ECDSA-P256 leaf on disk;
//!   4. the leaf is loaded, CACHED in memory (and persisted per-SNI on disk so a
//!      restart reuses it), and returned as a per-connection pool: the boot
//!      Ed25519 default plus this SNI's freshly minted ECDSA leaf. `chooseCert`
//!      presents the ECDSA leaf to any real client (its `signature_algorithms`
//!      never offer Ed25519), and since we minted for THIS connection's peeked
//!      SNI the presented leaf names the host.
//!
//! Nothing here parses a TLS record beyond the one-shot SNI peek, touches a key,
//! or speaks the ACME protocol — the mint is the verified driver in a subprocess.
//!
//! ## Single-flight and rate-limiting
//!
//! Concurrent first-hits for the SAME SNI must not each drive a full ACME order
//! (that hammers the CA and trips its rate limits). A per-SNI issuance lock
//! serializes them: the first thread mints, the rest wait on the lock and then
//! find the cache populated. A denial or a failed mint is negatively cached with
//! a cooldown so a hostile or broken SNI cannot drive an order per handshake.
//!
//! Gated entirely on `DRORB_TLS_ONDEMAND` (the ACME directory URL). Unset ⇒ this
//! module is inert and every connection is served the boot pool unchanged.

use std::collections::HashMap;
use std::process::Command;
use std::sync::{Arc, Mutex, OnceLock};
use std::time::{Duration, Instant, SystemTime};

/// A minted (or reloaded) per-SNI ECDSA-P256 leaf: the DER end-entity
/// certificate and its 32-byte raw signing scalar, in the exact shape
/// [`crate::tls::TlsCert`]'s ECDSA slot wants.
pub struct SniCert {
    pub cert_der: Vec<u8>,
    pub priv_scalar: Vec<u8>,
}

/// What [`resolve`] decided for one connection's SNI.
pub enum Resolution {
    /// Serve this connection a per-connection pool carrying this leaf.
    Serve(Arc<SniCert>),
    /// The authorizer refused this host, or minting failed — drop the handshake.
    Refuse,
    /// Not an on-demand candidate (disabled, no/invalid SNI): serve the boot pool.
    Passthrough,
}

/// On-demand configuration, resolved once from the environment.
struct Cfg {
    /// ACME directory URL — also the gate (unset ⇒ on-demand off).
    dir_url: String,
    /// The authorizer endpoint base, e.g. `http://gateway:8080/internal/site-exists`.
    /// Unset ⇒ every syntactically valid SNI is allowed to mint (test posture).
    ask_url: Option<String>,
    /// The static root the HTTP-01 challenge is written into and served from.
    webroot: String,
    /// Where per-SNI minted material is written and persisted (`<dir>/<sni>/…`).
    cache_dir: String,
    /// The verified issuance executable (`acme-issue`).
    issue_bin: String,
    contact: Option<String>,
    account_key: Option<String>,
    /// After a denial or a failed mint, how long before we try that SNI again.
    cooldown: Duration,
}

/// A cached decision for one SNI.
enum Entry {
    /// A usable leaf; every subsequent handshake for this SNI reuses it — unless
    /// a sweep/renewal has since written a NEWER leaf on disk, detected by the
    /// modification time of the last-written file (`ecdsa-key.bin`) that produced
    /// this `Arc`. A newer on-disk mtime triggers a live reload
    /// ([`reload_into_cache`]) so the fresh leaf is served without a restart.
    Ready {
        cert: Arc<SniCert>,
        /// mtime of `<cache>/<sni>/ecdsa-key.bin` when this `Arc` was loaded.
        mtime: Option<SystemTime>,
    },
    /// The authorizer said no (until this instant).
    Denied(Instant),
    /// A mint attempt failed (retry allowed after this instant).
    Failed(Instant),
}

struct State {
    cfg: Cfg,
    cache: Mutex<HashMap<String, Entry>>,
    /// Per-SNI single-flight locks (get-or-create under `locks`).
    locks: Mutex<HashMap<String, Arc<Mutex<()>>>>,
}

fn env_opt(k: &str) -> Option<String> {
    std::env::var(k).ok().filter(|s| !s.is_empty())
}

fn cfg() -> Option<Cfg> {
    let dir_url = env_opt("DRORB_TLS_ONDEMAND")?;
    let cache_dir = env_opt("DRORB_TLS_ONDEMAND_DIR").unwrap_or_else(|| "ondemand-tls".to_string());
    let webroot = env_opt("DRORB_TLS_ONDEMAND_WEBROOT")
        .or_else(|| env_opt("DRORB_ACME_WEBROOT"))
        .unwrap_or_else(|| cache_dir.clone());
    let cooldown = env_opt("DRORB_TLS_ONDEMAND_COOLDOWN")
        .and_then(|v| v.parse::<u64>().ok())
        .map(Duration::from_secs)
        .unwrap_or_else(|| Duration::from_secs(300));
    Some(Cfg {
        dir_url,
        ask_url: env_opt("DRORB_TLS_ONDEMAND_ASK"),
        webroot,
        cache_dir,
        issue_bin: env_opt("DRORB_ACME_ISSUE_BIN")
            .unwrap_or_else(|| ".lake/build/bin/acme-issue".to_string()),
        contact: env_opt("DRORB_ACME_CONTACT"),
        account_key: env_opt("DRORB_ACME_ACCOUNT_KEY"),
        cooldown,
    })
}

fn state() -> Option<&'static State> {
    static STATE: OnceLock<Option<State>> = OnceLock::new();
    STATE
        .get_or_init(|| {
            cfg().map(|cfg| {
                eprintln!(
                    "dataplane: on-demand TLS enabled — dir={}, ask={}, cache={}, webroot={}",
                    cfg.dir_url,
                    cfg.ask_url.as_deref().unwrap_or("(none: allow-all)"),
                    cfg.cache_dir,
                    cfg.webroot
                );
                State {
                    cfg,
                    cache: Mutex::new(HashMap::new()),
                    locks: Mutex::new(HashMap::new()),
                }
            })
        })
        .as_ref()
}

/// Is on-demand issuance configured at all?
pub fn enabled() -> bool {
    state().is_some()
}

/// A syntactically plausible DNS host name (defensive — an SNI is attacker
/// controlled and becomes a subprocess argument and a path component). Letters,
/// digits, `-`, `.`, `*`, `_`; 1..=253 bytes; no path separators or `..`.
fn valid_host(h: &str) -> bool {
    !h.is_empty()
        && h.len() <= 253
        && !h.contains("..")
        && h.bytes()
            .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'-' | b'.' | b'*' | b'_'))
}

/// Decide what to serve a connection whose peeked SNI is `sni`.
pub fn resolve(sni: &str) -> Resolution {
    let Some(st) = state() else {
        return Resolution::Passthrough;
    };
    if !valid_host(sni) {
        return Resolution::Passthrough;
    }

    // Fast path: a decision is already cached. For a Ready leaf this ALSO honors
    // a newer on-disk leaf (a renewal sweep re-minted it) by hot-reloading the
    // in-memory Arc — so a swept SNI serves its fresh leaf with no restart.
    if let Some(r) = serve_cached(st, sni) {
        return r;
    }

    // Single-flight: one issuance per SNI at a time. Concurrent first-hits for
    // the same host serialize here; the losers re-check the cache and find the
    // winner's leaf rather than driving their own ACME order.
    let lock = sni_lock(st, sni);
    let _guard = lock.lock().unwrap_or_else(|e| e.into_inner());

    // Re-check under the lock — the thread that held it may have just finished.
    if let Some(r) = serve_cached(st, sni) {
        return r;
    }

    // Authorizer gate (RFC-less internal ask). No endpoint ⇒ allow-all.
    if let Some(ask) = &st.cfg.ask_url {
        match ask_site_exists(ask, sni) {
            Some(true) => {}
            Some(false) => {
                eprintln!(
                    "dataplane: on-demand TLS — authorizer refused {sni}; dropping handshake"
                );
                store(st, sni, Entry::Denied(Instant::now() + st.cfg.cooldown));
                return Resolution::Refuse;
            }
            None => {
                eprintln!(
                    "dataplane: on-demand TLS — authorizer {ask} unreachable for {sni}; dropping"
                );
                store(st, sni, Entry::Failed(Instant::now() + st.cfg.cooldown));
                return Resolution::Refuse;
            }
        }
    }

    // Disk reuse: a prior run (or a prior process) may already hold this leaf.
    if let Some((cert, mtime)) = load_from_disk(&st.cfg, sni) {
        eprintln!("dataplane: on-demand TLS — {sni} served from the persisted cache");
        let arc = Arc::new(cert);
        store(
            st,
            sni,
            Entry::Ready {
                cert: Arc::clone(&arc),
                mtime,
            },
        );
        return Resolution::Serve(arc);
    }

    // Mint it: the verified ACME driver, HTTP-01 served from the webroot.
    match mint(&st.cfg, sni) {
        Ok((cert, mtime)) => {
            eprintln!("dataplane: on-demand TLS — MINTED a leaf for {sni}");
            let arc = Arc::new(cert);
            store(
                st,
                sni,
                Entry::Ready {
                    cert: Arc::clone(&arc),
                    mtime,
                },
            );
            Resolution::Serve(arc)
        }
        Err(e) => {
            eprintln!("dataplane: on-demand TLS — mint FAILED for {sni}: {e}");
            store(st, sni, Entry::Failed(Instant::now() + st.cfg.cooldown));
            Resolution::Refuse
        }
    }
}

/// A cached decision for `sni`, honoring negative-cache cooldowns, AND picking up
/// a leaf a renewal sweep has re-minted on disk since this `Arc` was cached.
/// Returns `None` when there is no live decision (so the caller proceeds to mint).
///
/// A Ready leaf is served from memory. Before doing so we cheaply stat the
/// last-written leaf file (`ecdsa-key.bin`); if its mtime is newer than the one
/// this `Arc` was loaded with, a sweep re-minted — so we reload from disk and
/// atomically swap in the fresh leaf. The disk read happens OUTSIDE the cache lock
/// (only a brief lock brackets the pointer swap); a reload that finds nothing
/// usable (a torn/half-written re-mint) keeps serving the still-valid cached leaf,
/// so a handshake mid-reload never sees a gap.
fn serve_cached(st: &State, sni: &str) -> Option<Resolution> {
    // Snapshot the current decision under a brief lock (no disk I/O held).
    let (arc, stored_mtime) = {
        let mut cache = st.cache.lock().unwrap_or_else(|e| e.into_inner());
        match cache.get(sni) {
            Some(Entry::Ready { cert, mtime }) => (Arc::clone(cert), *mtime),
            Some(Entry::Denied(until) | Entry::Failed(until)) if Instant::now() < *until => {
                return Some(Resolution::Refuse);
            }
            Some(Entry::Denied(_) | Entry::Failed(_)) => {
                cache.remove(sni); // cooldown elapsed: allow a fresh attempt
                return None;
            }
            None => return None,
        }
    };
    // Ready: serve from memory, but first pick up a newer on-disk leaf if a sweep
    // re-minted one (cheap mtime stat, no lock held).
    if disk_is_newer(&st.cfg, sni, stored_mtime) {
        if let Some(fresh) = reload_into_cache(st, sni) {
            return Some(Resolution::Serve(fresh));
        }
        // Nothing usable on disk yet (a re-mint still in flight): fall through and
        // serve the still-valid cached leaf rather than gap the connection.
    }
    Some(Resolution::Serve(arc))
}

/// mtime of the last file a mint/re-mint writes (`ecdsa-key.bin`). Keyed on the
/// LAST-written file so that when it advances the companion `ecdsa-cert.der`
/// (written first) is already complete — a reload never pairs a new cert with an
/// old key.
fn key_mtime(cfg: &Cfg, sni: &str) -> Option<SystemTime> {
    std::fs::metadata(format!("{}/{}/ecdsa-key.bin", cfg.cache_dir, sni))
        .ok()?
        .modified()
        .ok()
}

/// Has a newer leaf landed on disk since the cached `Arc` was loaded?
fn disk_is_newer(cfg: &Cfg, sni: &str, stored: Option<SystemTime>) -> bool {
    match (key_mtime(cfg, sni), stored) {
        (Some(disk), Some(cur)) => disk > cur,
        (Some(_), None) => true, // no recorded mtime: reload once to record it
        (None, _) => false,      // can't stat: don't churn
    }
}

/// Reload `sni`'s leaf from disk and atomically swap it into the cache. Serialized
/// per-SNI (reusing the issuance lock) so concurrent handshakes don't stampede the
/// disk. Returns the fresh `Arc` on success, `None` when nothing usable is on disk
/// (a torn/partial re-mint) — the caller then keeps serving the current leaf. The
/// swap is a single insert under the cache lock, so a concurrent reader sees either
/// the whole old `Arc` or the whole new one, never a torn read.
fn reload_into_cache(st: &State, sni: &str) -> Option<Arc<SniCert>> {
    let lock = sni_lock(st, sni);
    let _guard = lock.lock().unwrap_or_else(|e| e.into_inner());
    let (cert, mtime) = load_from_disk(&st.cfg, sni)?;
    let arc = Arc::new(cert);
    st.cache.lock().unwrap_or_else(|e| e.into_inner()).insert(
        sni.to_string(),
        Entry::Ready {
            cert: Arc::clone(&arc),
            mtime,
        },
    );
    Some(arc)
}

/// Signal from the renewal sweep (`renewal.rs`) that it re-minted `sni`'s leaf on
/// disk: reload it into the live cache so the very next handshake serves the fresh
/// leaf WITHOUT a restart. The sweep calls this only AFTER the issuer subprocess
/// has exited, so both leaf files are complete and the reload is never torn. A
/// no-op when on-demand is disabled or `sni` is not a valid host. Returns whether a
/// fresh leaf was swapped in (`false` ⇒ nothing usable on disk; current leaf stands).
pub fn reload_sni(sni: &str) -> bool {
    let Some(st) = state() else {
        return false;
    };
    if !valid_host(sni) {
        return false;
    }
    reload_into_cache(st, sni).is_some()
}

fn store(st: &State, sni: &str, e: Entry) {
    st.cache
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .insert(sni.to_string(), e);
}

fn sni_lock(st: &State, sni: &str) -> Arc<Mutex<()>> {
    let mut locks = st.locks.lock().unwrap_or_else(|e| e.into_inner());
    Arc::clone(locks.entry(sni.to_string()).or_default())
}

/// Load a persisted per-SNI leaf if present and structurally usable (a 32-byte
/// scalar), together with the mtime of its last-written file (`ecdsa-key.bin`),
/// which tags the `Arc` so a later sweep-written leaf is detected. Expiry is not
/// re-checked here — the renewal scheduler owns that; a stale disk leaf is at
/// worst a failed handshake that re-mints after cooldown.
///
/// The cert is read BEFORE the key and the freshness tag is the key's mtime:
/// since a mint/re-mint writes the cert first and the key last, a key whose mtime
/// we honor is always paired with a fully-written cert — never a torn new-cert /
/// old-key mix. A half-written re-mint (short/absent key) reads as `None`, so the
/// caller keeps serving the current leaf.
fn load_from_disk(cfg: &Cfg, sni: &str) -> Option<(SniCert, Option<SystemTime>)> {
    let dir = format!("{}/{}", cfg.cache_dir, sni);
    let cert_der = std::fs::read(format!("{dir}/ecdsa-cert.der")).ok()?;
    let priv_scalar = std::fs::read(format!("{dir}/ecdsa-key.bin")).ok()?;
    if cert_der.is_empty() || priv_scalar.len() != 32 {
        return None;
    }
    let mtime = key_mtime(cfg, sni);
    Some((
        SniCert {
            cert_der,
            priv_scalar,
        },
        mtime,
    ))
}

/// Drive the verified ACME issuer for `sni`, writing into `<cache_dir>/<sni>`,
/// then load the leaf it produced (with its freshness mtime).
fn mint(cfg: &Cfg, sni: &str) -> Result<(SniCert, Option<SystemTime>), String> {
    let outdir = format!("{}/{}", cfg.cache_dir, sni);
    std::fs::create_dir_all(&outdir).map_err(|e| format!("mkdir {outdir}: {e}"))?;
    std::fs::create_dir_all(&cfg.webroot)
        .map_err(|e| format!("mkdir webroot {}: {e}", cfg.webroot))?;

    let mut cmd = Command::new(&cfg.issue_bin);
    cmd.arg(&cfg.dir_url)
        .arg(sni)
        .arg(&cfg.webroot)
        .arg(&outdir);
    if let Some(c) = &cfg.contact {
        cmd.arg(c);
    }
    if let Some(k) = &cfg.account_key {
        cmd.env("DRORB_ACME_ACCOUNT_KEY", k);
    }
    let status = cmd
        .status()
        .map_err(|e| format!("spawn {}: {e}", cfg.issue_bin))?;
    if !status.success() {
        return Err(format!("{} exited {status}", cfg.issue_bin));
    }
    load_from_disk(cfg, sni).ok_or_else(|| {
        format!(
            "{} succeeded but wrote no usable leaf under {outdir}",
            cfg.issue_bin
        )
    })
}

/// The internal authorizer call: `GET <ask>?domain=<sni>` over plaintext HTTP/1.1
/// to a local backend (Caddy's `on_demand_tls { ask … }`). `Some(true)` on a 2xx,
/// `Some(false)` on any other status, `None` when the backend is unreachable.
///
/// This is an internal, plaintext call to a co-located trusted backend — not a
/// TLS path and not a place crypto belongs; a std TCP request is the whole of it.
fn ask_site_exists(ask: &str, sni: &str) -> Option<bool> {
    let (host, port, path) = split_http_url(ask)?;
    let sep = if path.contains('?') { '&' } else { '?' };
    let req = format!(
        "GET {path}{sep}domain={sni} HTTP/1.1\r\nHost: {host}\r\nConnection: close\r\nAccept: */*\r\n\r\n"
    );
    use std::io::{Read, Write};
    let mut stream = std::net::TcpStream::connect((host.as_str(), port)).ok()?;
    stream.set_read_timeout(Some(Duration::from_secs(5))).ok()?;
    stream
        .set_write_timeout(Some(Duration::from_secs(5)))
        .ok()?;
    stream.write_all(req.as_bytes()).ok()?;
    let mut buf = Vec::with_capacity(512);
    let mut chunk = [0u8; 512];
    // The status line is all we need; read a little and stop.
    loop {
        match stream.read(&mut chunk) {
            Ok(0) => break,
            Ok(n) => {
                buf.extend_from_slice(&chunk[..n]);
                if buf.iter().any(|&b| b == b'\n') || buf.len() >= 4096 {
                    break;
                }
            }
            Err(_) => break,
        }
    }
    let head = String::from_utf8_lossy(&buf);
    let status = head
        .split_whitespace()
        .nth(1)
        .and_then(|c| c.parse::<u16>().ok())?;
    Some((200..300).contains(&status))
}

/// Split `http://host[:port]/path` into `(host, port, path)`. HTTP only (this is
/// the internal ask; TLS never rides it). Defaults to port 80 and path `/`.
fn split_http_url(url: &str) -> Option<(String, u16, String)> {
    let rest = url.strip_prefix("http://")?;
    let (authority, path) = match rest.find('/') {
        Some(i) => (&rest[..i], &rest[i..]),
        None => (rest, "/"),
    };
    let (host, port) = match authority.rsplit_once(':') {
        Some((h, p)) => (h.to_string(), p.parse::<u16>().ok()?),
        None => (authority.to_string(), 80),
    };
    if host.is_empty() {
        return None;
    }
    Some((host, port, path.to_string()))
}

// --- ClientHello SNI peek -------------------------------------------------- //

/// Extract the SNI host_name from a TLS ClientHello record. UNTRUSTED
/// provisioning hint: the proven parser re-reads it authoritatively. Returns
/// `None` on anything that is not a single well-formed ClientHello carrying a
/// `host_name` server_name (the caller then serves the boot pool).
pub fn parse_client_hello_sni(rec: &[u8]) -> Option<String> {
    // TLS record: type(1)=22 handshake, version(2), length(2), fragment.
    let (rtype, rest) = rec.split_first()?;
    if *rtype != 22 {
        return None;
    }
    let rlen = be16(rest.get(2)?, rest.get(3)?) as usize;
    let frag = rest.get(4..4 + rlen.min(rest.len().saturating_sub(4)))?;
    // Handshake: msg_type(1)=1 ClientHello, length(3), body.
    let (&htype, hrest) = frag.split_first()?;
    if htype != 1 {
        return None;
    }
    let body = hrest.get(3..)?; // skip the 3-byte handshake length
    let mut p = 0usize;
    p += 2; // legacy_version
    p += 32; // random
    let sid_len = *body.get(p)? as usize;
    p += 1 + sid_len; // session_id
    let cs_len = be16(body.get(p)?, body.get(p + 1)?) as usize;
    p += 2 + cs_len; // cipher_suites
    let comp_len = *body.get(p)? as usize;
    p += 1 + comp_len; // compression_methods
    let ext_total = be16(body.get(p)?, body.get(p + 1)?) as usize;
    p += 2;
    let exts = body.get(p..p + ext_total)?;
    parse_extensions_sni(exts)
}

fn parse_extensions_sni(mut exts: &[u8]) -> Option<String> {
    while exts.len() >= 4 {
        let etype = be16(&exts[0], &exts[1]);
        let elen = be16(&exts[2], &exts[3]) as usize;
        let edata = exts.get(4..4 + elen)?;
        if etype == 0 {
            // server_name: server_name_list<2>, then entries { type(1), name<2> }.
            let list_len = be16(edata.get(0)?, edata.get(1)?) as usize;
            let mut list = edata.get(2..2 + list_len)?;
            while list.len() >= 3 {
                let name_type = list[0];
                let name_len = be16(&list[1], &list[2]) as usize;
                let name = list.get(3..3 + name_len)?;
                if name_type == 0 {
                    return std::str::from_utf8(name)
                        .ok()
                        .map(|s| s.to_ascii_lowercase());
                }
                list = &list[3 + name_len..];
            }
            return None;
        }
        exts = &exts[4 + elen..];
    }
    None
}

fn be16(a: &u8, b: &u8) -> u16 {
    ((*a as u16) << 8) | (*b as u16)
}

/// Peek the first ClientHello on `fd` WITHOUT consuming it (`MSG_PEEK`), so the
/// proven server still reads the full handshake, and return its SNI. Bounded by a
/// short poll timeout so a peer that connects and stalls cannot pin the thread.
#[cfg(any(
    target_os = "linux",
    target_os = "macos",
    target_os = "ios",
    target_os = "freebsd",
    target_os = "netbsd",
    target_os = "openbsd",
    target_os = "dragonfly"
))]
pub fn peek_sni(fd: std::os::fd::RawFd) -> Option<String> {
    let mut pfd = libc::pollfd {
        fd,
        events: libc::POLLIN,
        revents: 0,
    };
    // Up to ~2s for the first flight to arrive.
    let n = unsafe { libc::poll(&mut pfd, 1, 2000) };
    if n <= 0 || (pfd.revents & libc::POLLIN) == 0 {
        return None;
    }
    let mut buf = vec![0u8; 4096];
    let got = unsafe {
        libc::recv(
            fd,
            buf.as_mut_ptr() as *mut libc::c_void,
            buf.len(),
            libc::MSG_PEEK,
        )
    };
    if got <= 0 {
        return None;
    }
    parse_client_hello_sni(&buf[..got as usize])
}

#[cfg(not(any(
    target_os = "linux",
    target_os = "macos",
    target_os = "ios",
    target_os = "freebsd",
    target_os = "netbsd",
    target_os = "openbsd",
    target_os = "dragonfly"
)))]
pub fn peek_sni(_fd: std::os::fd::RawFd) -> Option<String> {
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn url_split() {
        assert_eq!(
            split_http_url("http://gateway:8080/internal/site-exists"),
            Some(("gateway".into(), 8080, "/internal/site-exists".into()))
        );
        assert_eq!(
            split_http_url("http://127.0.0.1/x"),
            Some(("127.0.0.1".into(), 80, "/x".into()))
        );
        assert_eq!(
            split_http_url("http://h:9"),
            Some(("h".into(), 9, "/".into()))
        );
        assert_eq!(split_http_url("https://h/x"), None);
    }

    #[test]
    fn host_validation() {
        assert!(valid_host("a.apps.example.test"));
        assert!(valid_host("*.apps.example.test"));
        assert!(!valid_host(""));
        assert!(!valid_host("../etc/passwd"));
        assert!(!valid_host("a/b"));
        assert!(!valid_host("a b"));
    }

    /// A hand-built minimal ClientHello with an SNI extension parses to the host.
    #[test]
    fn client_hello_sni() {
        let host = b"a.apps.example.test";
        // server_name entry: type(0) + name<2>
        let mut sni_ext_data = vec![0u8]; // name_type = host_name
        sni_ext_data.extend_from_slice(&(host.len() as u16).to_be_bytes());
        sni_ext_data.extend_from_slice(host);
        // server_name_list<2>
        let mut sn = (sni_ext_data.len() as u16).to_be_bytes().to_vec();
        sn.extend_from_slice(&sni_ext_data);
        // extension: type(0) + len<2> + data
        let mut ext = vec![0u8, 0u8];
        ext.extend_from_slice(&(sn.len() as u16).to_be_bytes());
        ext.extend_from_slice(&sn);
        // extensions<2>
        let mut exts = (ext.len() as u16).to_be_bytes().to_vec();
        exts.extend_from_slice(&ext);
        // ClientHello body
        let mut body = vec![0x03, 0x03]; // legacy_version
        body.extend_from_slice(&[0u8; 32]); // random
        body.push(0); // session_id len
        body.extend_from_slice(&[0u8, 2, 0x13, 0x01]); // cipher_suites<2> = one suite
        body.extend_from_slice(&[1u8, 0u8]); // compression_methods<1> = null
        body.extend_from_slice(&exts);
        // Handshake header: type(1)=1 + length(3)
        let mut hs = vec![1u8];
        hs.extend_from_slice(&[
            ((body.len() >> 16) & 0xff) as u8,
            ((body.len() >> 8) & 0xff) as u8,
            (body.len() & 0xff) as u8,
        ]);
        hs.extend_from_slice(&body);
        // Record header: type(22) + version(2) + length(2)
        let mut rec = vec![22u8, 0x03, 0x01];
        rec.extend_from_slice(&(hs.len() as u16).to_be_bytes());
        rec.extend_from_slice(&hs);

        assert_eq!(
            parse_client_hello_sni(&rec).as_deref(),
            Some("a.apps.example.test")
        );
    }

    #[test]
    fn not_a_client_hello() {
        assert_eq!(parse_client_hello_sni(&[23, 3, 3, 0, 0]), None);
        assert_eq!(parse_client_hello_sni(&[]), None);
    }
}
