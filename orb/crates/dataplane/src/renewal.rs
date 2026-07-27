//! Automated certificate renewal: the background scheduler that keeps a
//! CA-issued leaf fresh without an operator and without a restart.
//!
//! Issuance itself (`acme-issue`, the RFC 8555 driver) lands a new leaf on disk;
//! the TLS front door already hot-reloads a changed pool ([`crate::tls::reload`],
//! and the file-watch in `tls.rs`). What was missing between the two is the
//! *scheduling*: nothing decided WHEN to re-issue, so a cert simply expired. This
//! module is that decision, carried out as untrusted shell:
//!
//!   1. read the served leaf's DER and parse its validity (`notBefore` /
//!      `notAfter`) — [`parse_validity`];
//!   2. renew when the remaining lifetime falls below a fraction of the whole
//!      (default 1/3 — LE is moving to 45-day certs, so ~15 days out) — the same
//!      "renew at 2/3 elapsed" discipline every ACME client uses;
//!   3. run the configured issuance command (`acme-issue`), which writes the new
//!      leaf where the TLS pool loads it;
//!   4. call [`crate::tls::reload`] so the very next handshake serves the new
//!      leaf — in-flight connections keep the leaf they handshook with (see the
//!      `CERTS` note in `tls.rs`), so the swap drops nothing.
//!
//! ## The on-demand cache sweep
//!
//! The configured-leaf path above renews ONE leaf. On-demand TLS
//! (`tls/ondemand.rs`) instead mints a leaf PER SNI on first handshake and
//! persists it under `<DRORB_TLS_ONDEMAND_DIR>/<sni>/`. Those leaves have the
//! same finite lifetime, but nothing watched them: an idle SNI's cert could
//! expire un-renewed, and a busy one only re-minted reactively on the next
//! handshake after its negative-cache cooldown. So this scheduler ALSO sweeps
//! the on-demand cache each tick:
//!
//!   - enumerate `<cache_dir>/<sni>/ecdsa-cert.der`, parse each leaf's validity,
//!     and for any within `fraction` of expiry, proactively re-mint it via the
//!     SAME verified `acme-issue` flow on-demand uses (`dir_url sni webroot
//!     <cache_dir>/<sni>`) — a renewal is just a scheduled re-mint into the same
//!     per-SNI cache dir;
//!   - single-flight/rate-limit: the sweep runs on this one scheduler thread
//!     (serial, never concurrent re-mints), and a per-SNI minimum re-attempt
//!     interval (`DRORB_TLS_ONDEMAND_RENEW_COOLDOWN`) stops a failing renewal or
//!     a tight check interval from hammering the CA;
//!   - a failed re-mint changes nothing on disk beyond what `acme-issue` writes,
//!     so the still-valid current leaf keeps being served until it truly expires.
//!
//! A swept leaf is refreshed on disk AND the live in-memory on-demand cache is
//! hot-reloaded for that SNI ([`crate::tls::ondemand::reload_sni`], called right
//! after the issuer exits so both leaf files are complete): the very next
//! handshake serves the fresh leaf with NO process restart. In-flight
//! connections keep the leaf they handshook with. The sweep is gated on
//! `DRORB_TLS_ONDEMAND` independently of the configured-leaf `DRORB_ACME_RENEW`,
//! so either or both may drive the thread.
//!
//! ## What is and is not in this file
//!
//! This is the SHELL: it parses a date to pick a time, runs a subprocess, and
//! calls the already-wired reload. It performs no cryptography and speaks no TLS.
//! The certificate is minted by `acme-issue` — whose CA transport is the ACME
//! client lane's residual — over the verified JWS/ES256/CSR core; the leaf it
//! writes is the one the verified server later presents. The validity parse here
//! only decides a *timer*; a misparse can only renew early or late, never change
//! what is served or trusted, so it is scheduling metadata, not a security
//! decision.
//!
//! The scheduler thread starts if EITHER driver is configured: the
//! configured-leaf renewal on `DRORB_ACME_RENEW`, or the on-demand cache sweep
//! on `DRORB_TLS_ONDEMAND` (the ACME directory URLs). With neither set it never
//! starts and this file is inert.

use std::collections::HashMap;
use std::process::Command;
use std::sync::atomic::Ordering;
use std::time::Duration;

/// The resolved renewal configuration, read once from the environment.
struct RenewCfg {
    /// ACME directory URL — also the gate (unset ⇒ no scheduler).
    dir_url: String,
    /// The identifier (domain) to issue for.
    domain: String,
    /// The static root the HTTP-01 challenge is served from.
    webroot: String,
    /// Where the issuance command writes the new leaf (must be where the TLS
    /// pool loads `DRORB_TLS_ECDSA_CERT` / `_KEY` from, or the reload is a no-op).
    outdir: String,
    /// The issuance executable (default `.lake/build/bin/acme-issue`).
    issue_bin: String,
    /// Optional ACME contact email.
    contact: Option<String>,
    /// Optional durable account-key path, passed to the issuer so re-runs reuse
    /// the same ACME account (`DRORB_ACME_ACCOUNT_KEY`).
    account_key: Option<String>,
    /// The leaf DER whose validity drives the schedule (default
    /// `DRORB_TLS_ECDSA_CERT`, else `<outdir>/ecdsa-cert.der`).
    leaf_path: String,
    /// Renew once the remaining lifetime is below this fraction of the whole.
    fraction: f64,
    /// Seconds between schedule checks.
    check_secs: u64,
}

/// The on-demand cache sweep configuration, resolved from the on-demand env
/// (shared with `tls/ondemand.rs` — the sweep re-mints into the same per-SNI
/// cache dirs via the same issuer, so its inputs must match).
struct SweepCfg {
    /// ACME directory URL — also the gate (`DRORB_TLS_ONDEMAND` unset ⇒ no sweep).
    dir_url: String,
    /// Root of the per-SNI cache (`<cache_dir>/<sni>/ecdsa-cert.der`).
    cache_dir: String,
    /// The static root the HTTP-01 challenge is served from during a re-mint.
    webroot: String,
    /// The issuance executable (same `acme-issue` on-demand mints with).
    issue_bin: String,
    /// Optional ACME contact email.
    contact: Option<String>,
    /// Optional durable account-key path (`DRORB_ACME_ACCOUNT_KEY`).
    account_key: Option<String>,
    /// Re-mint a cached leaf once its remaining lifetime is below this fraction.
    fraction: f64,
    /// Minimum seconds between re-mint ATTEMPTS for the same SNI — the rate limit
    /// that keeps a failing renewal (or a tight check interval) from hammering
    /// the CA (`DRORB_TLS_ONDEMAND_RENEW_COOLDOWN`, default 6h).
    min_reattempt: u64,
}

/// Read `env`, falling back to `default`.
fn env_or(env: &str, default: &str) -> String {
    std::env::var(env).unwrap_or_else(|_| default.to_string())
}

/// A non-empty environment value, or `None`.
fn env_opt(k: &str) -> Option<String> {
    std::env::var(k).ok().filter(|s| !s.is_empty())
}

/// The renew fraction (`DRORB_ACME_RENEW_FRACTION`), default 1/3, clamped to
/// `(0, 1)`. Shared by the configured-leaf schedule and the on-demand sweep so
/// both renew on the same "< a third of lifetime remaining" discipline.
fn env_fraction() -> f64 {
    std::env::var("DRORB_ACME_RENEW_FRACTION")
        .ok()
        .and_then(|v| v.parse::<f64>().ok())
        .filter(|f| *f > 0.0 && *f < 1.0)
        .unwrap_or(1.0 / 3.0)
}

/// Seconds between schedule ticks (`DRORB_ACME_CHECK_SECS`), default 1h.
fn env_check_secs() -> u64 {
    std::env::var("DRORB_ACME_CHECK_SECS")
        .ok()
        .and_then(|v| v.parse::<u64>().ok())
        .filter(|s| *s > 0)
        .unwrap_or(3600)
}

/// Force one immediate renewal on the first tick (`DRORB_ACME_RENEW_NOW=1`) —
/// the my-hand demo lever; drives both the configured leaf and the sweep.
fn env_force_now() -> bool {
    std::env::var("DRORB_ACME_RENEW_NOW").as_deref() == Ok("1")
}

/// The directory component of a path (everything before the last `/`), or `.`.
fn dirname(path: &str) -> &str {
    match path.rfind('/') {
        Some(0) => "/",
        Some(i) => &path[..i],
        None => ".",
    }
}

/// Resolve the renewal configuration from the environment, or `None` when the
/// scheduler is disabled (`DRORB_ACME_RENEW` unset) or under-configured.
fn cfg() -> Option<RenewCfg> {
    let dir_url = std::env::var("DRORB_ACME_RENEW").ok()?;
    let domain = match std::env::var("DRORB_ACME_DOMAIN") {
        Ok(d) if !d.is_empty() => d,
        _ => {
            eprintln!(
                "dataplane: ACME renewal disabled — DRORB_ACME_RENEW is set but DRORB_ACME_DOMAIN is not"
            );
            return None;
        }
    };
    let outdir = match std::env::var("DRORB_ACME_OUTDIR") {
        Ok(d) if !d.is_empty() => d,
        _ => dirname(&env_or(
            "DRORB_TLS_ECDSA_CERT",
            "conformance/tls/ecdsa-cert.der",
        ))
        .to_string(),
    };
    let webroot = env_or("DRORB_ACME_WEBROOT", &outdir);
    let leaf_path = match std::env::var("DRORB_TLS_ECDSA_CERT") {
        Ok(p) if !p.is_empty() => p,
        _ => format!("{outdir}/ecdsa-cert.der"),
    };
    Some(RenewCfg {
        dir_url,
        domain,
        webroot,
        outdir,
        issue_bin: env_or("DRORB_ACME_ISSUE_BIN", ".lake/build/bin/acme-issue"),
        contact: env_opt("DRORB_ACME_CONTACT"),
        account_key: env_opt("DRORB_ACME_ACCOUNT_KEY"),
        leaf_path,
        fraction: env_fraction(),
        check_secs: env_check_secs(),
    })
}

/// Resolve the on-demand sweep configuration, or `None` when on-demand TLS is
/// disabled (`DRORB_TLS_ONDEMAND` unset). Mirrors `tls/ondemand.rs`'s own env
/// resolution so a scheduled re-mint lands in the exact same per-SNI cache dir.
fn sweep_cfg() -> Option<SweepCfg> {
    let dir_url = env_opt("DRORB_TLS_ONDEMAND")?;
    let cache_dir = env_opt("DRORB_TLS_ONDEMAND_DIR").unwrap_or_else(|| "ondemand-tls".to_string());
    let webroot = env_opt("DRORB_TLS_ONDEMAND_WEBROOT")
        .or_else(|| env_opt("DRORB_ACME_WEBROOT"))
        .unwrap_or_else(|| cache_dir.clone());
    let min_reattempt = env_opt("DRORB_TLS_ONDEMAND_RENEW_COOLDOWN")
        .and_then(|v| v.parse::<u64>().ok())
        .filter(|s| *s > 0)
        .unwrap_or(6 * 3600);
    Some(SweepCfg {
        dir_url,
        cache_dir,
        webroot,
        issue_bin: env_or("DRORB_ACME_ISSUE_BIN", ".lake/build/bin/acme-issue"),
        contact: env_opt("DRORB_ACME_CONTACT"),
        account_key: env_opt("DRORB_ACME_ACCOUNT_KEY"),
        fraction: env_fraction(),
        min_reattempt,
    })
}

/// A syntactically plausible DNS host: an SNI-shaped cache subdir name that is
/// safe to pass to a subprocess and use as a path component. Mirrors
/// `ondemand::valid_host` (the dir was created from a peeked SNI; re-check
/// defensively in case something else dropped a directory in the cache).
fn plausible_sni(h: &str) -> bool {
    !h.is_empty()
        && h.len() <= 253
        && !h.contains("..")
        && h.bytes()
            .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'-' | b'.' | b'*' | b'_'))
}

/// Seconds since the Unix epoch, now.
fn unix_now() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0)
}

// --- minimal ASN.1 / X.509 validity parsing -------------------------------- //
//
// Enough DER to walk to `Validity` and read its two `Time`s. This is scheduling
// metadata (see the module note): it only chooses when the timer fires.

/// One DER TLV: its tag, the content bytes, and the offset just past it.
struct Tlv<'a> {
    tag: u8,
    content: &'a [u8],
    end: usize,
}

/// Read the TLV at `off` in `buf` (definite lengths only, short or long form).
fn read_tlv(buf: &[u8], off: usize) -> Option<Tlv<'_>> {
    let tag = *buf.get(off)?;
    let len_byte = *buf.get(off + 1)?;
    let (len, hdr) = if len_byte < 0x80 {
        (len_byte as usize, 2)
    } else {
        let n = (len_byte & 0x7f) as usize;
        if n == 0 || n > 4 {
            return None; // indefinite or absurd length: not valid DER here
        }
        let mut len = 0usize;
        for i in 0..n {
            len = (len << 8) | *buf.get(off + 2 + i)? as usize;
        }
        (len, 2 + n)
    };
    let start = off + hdr;
    let end = start.checked_add(len)?;
    if end > buf.len() {
        return None;
    }
    Some(Tlv {
        tag,
        content: &buf[start..end],
        end,
    })
}

/// Parse an X.509 leaf's `(notBefore, notAfter)` as Unix seconds.
///
/// Certificate → tbsCertificate → { [0] version?, serial, sigAlg, issuer,
/// **validity**, ... }. We enter the two outer SEQUENCEs, then skip TBS fields
/// positionally until the `validity` SEQUENCE, and read its two `Time`s.
fn parse_validity(der: &[u8]) -> Option<(i64, i64)> {
    let cert = read_tlv(der, 0)?; // Certificate SEQUENCE
    if cert.tag != 0x30 {
        return None;
    }
    let tbs = read_tlv(cert.content, 0)?; // TBSCertificate SEQUENCE
    if tbs.tag != 0x30 {
        return None;
    }
    let body = tbs.content;
    let mut off = 0usize;
    // Optional [0] EXPLICIT version.
    let first = read_tlv(body, off)?;
    if first.tag == 0xA0 {
        off = first.end;
    }
    // serialNumber INTEGER
    off = read_tlv(body, off)?.end;
    // signature AlgorithmIdentifier SEQUENCE
    off = read_tlv(body, off)?.end;
    // issuer Name SEQUENCE
    off = read_tlv(body, off)?.end;
    // validity SEQUENCE { notBefore Time, notAfter Time }
    let validity = read_tlv(body, off)?;
    if validity.tag != 0x30 {
        return None;
    }
    let nb = read_tlv(validity.content, 0)?;
    let not_before = parse_asn1_time(nb.tag, nb.content)?;
    let na = read_tlv(validity.content, nb.end)?;
    let not_after = parse_asn1_time(na.tag, na.content)?;
    Some((not_before, not_after))
}

/// Days from the Unix epoch to `y-m-d` (proleptic Gregorian). Hinnant's
/// `days_from_civil`, exact for the whole range we care about.
fn days_from_civil(y: i64, m: i64, d: i64) -> i64 {
    let y = if m <= 2 { y - 1 } else { y };
    let era = (if y >= 0 { y } else { y - 399 }) / 400;
    let yoe = y - era * 400;
    let doy = (153 * (if m > 2 { m - 3 } else { m + 9 }) + 2) / 5 + d - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    era * 146097 + doe - 719468
}

/// Parse an ASN.1 `Time`: UTCTime (`0x17`, `YYMMDDHHMMSSZ`) or GeneralizedTime
/// (`0x18`, `YYYYMMDDHHMMSSZ`), UTC (`Z`) only — the profile RFC 5280 mandates
/// for certificate validity. Returns Unix seconds.
fn parse_asn1_time(tag: u8, content: &[u8]) -> Option<i64> {
    let s = std::str::from_utf8(content).ok()?;
    let s = s.strip_suffix('Z')?; // RFC 5280: certificate times are UTC
    let (year, rest) = match tag {
        0x17 => {
            // UTCTime: 2-digit year, 00-49 ⇒ 2000s, 50-99 ⇒ 1900s (RFC 5280).
            let yy: i64 = s.get(0..2)?.parse().ok()?;
            (if yy < 50 { 2000 + yy } else { 1900 + yy }, &s[2..])
        }
        0x18 => {
            // GeneralizedTime: 4-digit year.
            let yyyy: i64 = s.get(0..4)?.parse().ok()?;
            (yyyy, &s[4..])
        }
        _ => return None,
    };
    let mon: i64 = rest.get(0..2)?.parse().ok()?;
    let day: i64 = rest.get(2..4)?.parse().ok()?;
    let hour: i64 = rest.get(4..6)?.parse().ok()?;
    let min: i64 = rest.get(6..8)?.parse().ok()?;
    // Seconds are OPTIONAL in the general grammar; certificate times include them.
    let sec: i64 = rest.get(8..10).and_then(|x| x.parse().ok()).unwrap_or(0);
    if !(1..=12).contains(&mon) || !(1..=31).contains(&day) {
        return None;
    }
    Some(days_from_civil(year, mon, day) * 86400 + hour * 3600 + min * 60 + sec)
}

// --- the scheduler --------------------------------------------------------- //

/// The renewal decision for one tick: given now and the leaf's validity, is it
/// time to renew, and (for logging) how long is left. Renew once the remaining
/// lifetime is below `fraction` of the whole — or if the cert is already
/// expired, or its validity could not be read (renew rather than serve stale).
fn due(now: i64, not_before: i64, not_after: i64, fraction: f64) -> bool {
    let lifetime = (not_after - not_before).max(1);
    let remaining = not_after - now;
    remaining <= (lifetime as f64 * fraction) as i64
}

/// Run the issuance command once. Returns Ok on a zero exit, Err otherwise.
fn issue(cfg: &RenewCfg) -> Result<(), String> {
    let mut cmd = Command::new(&cfg.issue_bin);
    cmd.arg(&cfg.dir_url)
        .arg(&cfg.domain)
        .arg(&cfg.webroot)
        .arg(&cfg.outdir);
    if let Some(c) = &cfg.contact {
        cmd.arg(c);
    }
    if let Some(k) = &cfg.account_key {
        cmd.env("DRORB_ACME_ACCOUNT_KEY", k);
    }
    eprintln!(
        "dataplane: ACME renewal — issuing for {} via {} (out={})",
        cfg.domain, cfg.issue_bin, cfg.outdir
    );
    let status = cmd
        .status()
        .map_err(|e| format!("could not spawn {}: {e}", cfg.issue_bin))?;
    if status.success() {
        Ok(())
    } else {
        Err(format!("{} exited {status}", cfg.issue_bin))
    }
}

/// Attempt one renewal (issue → reload) and log the result. Isolated so both the
/// scheduled path and the forced path share it.
fn renew(cfg: &RenewCfg) {
    match issue(cfg) {
        Ok(()) => match crate::tls::reload() {
            Ok(tag) => eprintln!(
                "dataplane: ACME renewal COMPLETE — new leaf issued and hot-reloaded, pool={tag} \
                 (live connections undisturbed)"
            ),
            Err(e) => eprintln!(
                "dataplane: ACME renewal — issued, but the cert reload failed: {e} \
                 (the file-watch will retry)"
            ),
        },
        Err(e) => eprintln!("dataplane: ACME renewal FAILED (keeping the current cert): {e}"),
    }
}

/// Re-mint one on-demand SNI leaf: the SAME `acme-issue` invocation on-demand
/// mints with (`dir_url sni webroot <cache_dir>/<sni>`), so a renewal is exactly
/// a scheduled re-mint into that per-SNI cache dir. Returns Ok on a zero exit.
fn remint(cfg: &SweepCfg, sni: &str) -> Result<(), String> {
    let outdir = format!("{}/{}", cfg.cache_dir, sni);
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
    if status.success() {
        Ok(())
    } else {
        Err(format!("{} exited {status}", cfg.issue_bin))
    }
}

/// Sweep the on-demand per-SNI cache once: for each cached leaf within
/// `fraction` of expiry (or when `force`), proactively re-mint it. Serial (one
/// scheduler thread) and per-SNI rate-limited via `last_attempt` so a failing
/// renewal or a tight check interval cannot hammer the CA. A failed re-mint
/// leaves the still-valid current leaf in place.
fn sweep(cfg: &SweepCfg, now: i64, last_attempt: &mut HashMap<String, i64>, force: bool) {
    let rd = match std::fs::read_dir(&cfg.cache_dir) {
        Ok(rd) => rd,
        Err(e) => {
            // No cache dir yet (nothing minted on-demand) is the normal quiet case.
            if e.kind() != std::io::ErrorKind::NotFound {
                eprintln!(
                    "dataplane: on-demand sweep — cache dir {} unreadable: {e}",
                    cfg.cache_dir
                );
            }
            return;
        }
    };
    let mut examined = 0usize;
    let mut renewed = 0usize;
    for entry in rd.flatten() {
        if !entry.file_type().map(|t| t.is_dir()).unwrap_or(false) {
            continue;
        }
        let sni = entry.file_name().to_string_lossy().into_owned();
        if !plausible_sni(&sni) {
            continue;
        }
        let cert_path = format!("{}/{}/ecdsa-cert.der", cfg.cache_dir, sni);
        let der = match std::fs::read(&cert_path) {
            Ok(d) => d,
            Err(_) => continue, // no leaf here (a bare/partial dir): nothing to renew
        };
        let Some((nb, na)) = parse_validity(&der) else {
            // Unlike the single configured leaf (renew-on-misparse), an
            // unparseable entry in a directory of many is SKIPPED, not blindly
            // re-minted — that would let junk in the cache drive CA orders. A
            // genuinely broken leaf re-mints reactively on its next handshake.
            eprintln!("dataplane: on-demand sweep — {sni}: leaf unparseable; skipping");
            continue;
        };
        examined += 1;
        let remaining_days = (na - now) as f64 / 86400.0;
        if !(due(now, nb, na, cfg.fraction) || force) {
            continue;
        }
        if let Some(&last) = last_attempt.get(&sni) {
            if now - last < cfg.min_reattempt as i64 {
                eprintln!(
                    "dataplane: on-demand sweep — {sni}: due (notAfter in {remaining_days:.1}d) but re-attempted {}s ago (< {}s min); rate-limited, still serving the current leaf",
                    now - last,
                    cfg.min_reattempt
                );
                continue;
            }
        }
        eprintln!(
            "dataplane: on-demand sweep — {sni}: notAfter in {remaining_days:.1}d (< {:.0}% remaining); proactively re-minting via {}",
            cfg.fraction * 100.0,
            cfg.issue_bin
        );
        last_attempt.insert(sni.clone(), now);
        match remint(cfg, &sni) {
            Ok(()) => {
                renewed += 1;
                // Signal the live on-demand cache to hot-reload this SNI's fresh
                // leaf. The issuer subprocess has exited (both leaf files are
                // complete), so the reload is atomic and never torn; the very next
                // handshake for this SNI now serves the new leaf with NO restart.
                // (A running process holding no cached Arc for this SNI simply
                // loads the fresh leaf on its next handshake — reload is a no-op.)
                let reloaded = crate::tls::ondemand::reload_sni(&sni);
                eprintln!(
                    "dataplane: on-demand sweep — {sni}: RE-MINTED (fresh leaf written to the per-SNI cache; live in-memory cache hot-reload={reloaded}, served on the next handshake without a restart)"
                );
            }
            Err(e) => eprintln!(
                "dataplane: on-demand sweep — {sni}: renewal FAILED ({e}); keeping the still-valid current leaf until it truly expires"
            ),
        }
    }
    if examined > 0 {
        eprintln!(
            "dataplane: on-demand sweep — {examined} cached leaf/leaves examined, {renewed} re-minted"
        );
    }
}

/// One configured-leaf tick: read its validity and renew if due (or `force`).
fn tick_leaf(cfg: &RenewCfg, now: i64, force: bool) {
    let validity = std::fs::read(&cfg.leaf_path)
        .ok()
        .and_then(|der| parse_validity(&der));
    let should = match validity {
        Some((nb, na)) => {
            let remaining_days = (na - now) as f64 / 86400.0;
            let d = due(now, nb, na, cfg.fraction);
            eprintln!(
                "dataplane: ACME renewal check — leaf notAfter in {remaining_days:.1} day(s), due={d}"
            );
            d
        }
        None => {
            eprintln!(
                "dataplane: ACME renewal check — could not read/parse leaf {} validity; renewing",
                cfg.leaf_path
            );
            true
        }
    };
    if force {
        eprintln!("dataplane: ACME renewal — DRORB_ACME_RENEW_NOW forcing an immediate renewal");
    }
    if should || force {
        renew(cfg);
    }
}

/// The scheduler loop: on each tick, renew the configured leaf if due and sweep
/// the on-demand cache. Either driver may be absent. Sleeps `check_secs` between
/// ticks, waking early on shutdown.
fn scheduler(leaf: Option<RenewCfg>, sweep_c: Option<SweepCfg>, check_secs: u64, force_now: bool) {
    if let Some(c) = &leaf {
        eprintln!(
            "dataplane: ACME renewal scheduler up — domain={}, leaf={}, renew at <{:.0}% lifetime remaining, check every {}s",
            c.domain,
            c.leaf_path,
            c.fraction * 100.0,
            check_secs
        );
    }
    if let Some(s) = &sweep_c {
        eprintln!(
            "dataplane: on-demand cert sweep up — cache={}, renew at <{:.0}% lifetime remaining, min re-attempt {}s, check every {}s",
            s.cache_dir,
            s.fraction * 100.0,
            s.min_reattempt,
            check_secs
        );
    }
    // `DRORB_ACME_RENEW_NOW` forces the first tick of both; `DRORB_TLS_ONDEMAND_SWEEP_NOW`
    // forces only the sweep (useful when the configured leaf is not set up).
    let mut leaf_forced = force_now;
    let mut sweep_forced =
        force_now || std::env::var("DRORB_TLS_ONDEMAND_SWEEP_NOW").as_deref() == Ok("1");
    let mut last_attempt: HashMap<String, i64> = HashMap::new();
    loop {
        if crate::SHUTDOWN.load(Ordering::SeqCst) {
            return;
        }
        let now = unix_now();
        if let Some(c) = &leaf {
            tick_leaf(c, now, leaf_forced);
            leaf_forced = false;
        }
        if let Some(s) = &sweep_c {
            sweep(s, now, &mut last_attempt, sweep_forced);
            sweep_forced = false;
        }
        // Sleep in 1s slices so shutdown is observed within a second.
        for _ in 0..check_secs {
            if crate::SHUTDOWN.load(Ordering::SeqCst) {
                return;
            }
            std::thread::sleep(Duration::from_secs(1));
        }
    }
}

/// Start the renewal scheduler on its own thread, if either the configured-leaf
/// renewal (`DRORB_ACME_RENEW`) or the on-demand sweep (`DRORB_TLS_ONDEMAND`) is
/// configured. A no-op when neither is. Called once at boot from `main`.
pub fn install() {
    let leaf = cfg();
    let sweep_c = sweep_cfg();
    if leaf.is_none() && sweep_c.is_none() {
        return;
    }
    let check_secs = leaf
        .as_ref()
        .map(|c| c.check_secs)
        .unwrap_or_else(env_check_secs);
    let force_now = env_force_now();
    let _ = std::thread::Builder::new()
        .name("drorb-acme-renew".into())
        .spawn(move || scheduler(leaf, sweep_c, check_secs, force_now));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn utctime_and_generalized_parse() {
        // 2024-03-01T12:00:00Z
        let want = days_from_civil(2024, 3, 1) * 86400 + 12 * 3600;
        assert_eq!(parse_asn1_time(0x17, b"240301120000Z"), Some(want));
        assert_eq!(parse_asn1_time(0x18, b"20240301120000Z"), Some(want));
        // UTCTime year pivot: 49 ⇒ 2049, 50 ⇒ 1950.
        assert_eq!(
            parse_asn1_time(0x17, b"490101000000Z"),
            Some(days_from_civil(2049, 1, 1) * 86400)
        );
        assert_eq!(
            parse_asn1_time(0x17, b"500101000000Z"),
            Some(days_from_civil(1950, 1, 1) * 86400)
        );
    }

    #[test]
    fn due_at_one_third_remaining() {
        // 90-day cert; renew when < 1/3 (30 days) remain.
        let nb = 0i64;
        let na = 90 * 86400;
        assert!(!due(40 * 86400, nb, na, 1.0 / 3.0)); // 50 days left: no
        assert!(due(61 * 86400, nb, na, 1.0 / 3.0)); // 29 days left: yes
        assert!(due(100 * 86400, nb, na, 1.0 / 3.0)); // expired: yes
    }

    // --- on-demand cache sweep: DER builders + the sweep demo ------------- //

    /// Inverse of `days_from_civil` (Hinnant's `civil_from_days`): Unix day →
    /// `(y, m, d)`. Only used to synthesize a leaf whose validity is anchored to
    /// the real `now`, so the sweep demo exercises a genuine near-expiry leaf.
    fn civil_from_days(z: i64) -> (i64, i64, i64) {
        let z = z + 719468;
        let era = (if z >= 0 { z } else { z - 146096 }) / 146097;
        let doe = z - era * 146097;
        let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
        let y = yoe + era * 400;
        let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
        let mp = (5 * doy + 2) / 153;
        let d = doy - (153 * mp + 2) / 5 + 1;
        let m = if mp < 10 { mp + 3 } else { mp - 9 };
        (y + i64::from(m <= 2), m, d)
    }

    fn der_len(n: usize) -> Vec<u8> {
        if n < 0x80 {
            vec![n as u8]
        } else if n <= 0xff {
            vec![0x81, n as u8]
        } else {
            vec![0x82, (n >> 8) as u8, (n & 0xff) as u8]
        }
    }

    /// One DER TLV.
    fn tlv(tag: u8, content: &[u8]) -> Vec<u8> {
        let mut v = vec![tag];
        v.extend(der_len(content.len()));
        v.extend_from_slice(content);
        v
    }

    /// A GeneralizedTime (`0x18`, `YYYYMMDDHHMMSSZ`) TLV for a Unix timestamp.
    fn gtime(unix: i64) -> Vec<u8> {
        let (y, m, d) = civil_from_days(unix.div_euclid(86400));
        let s = unix.rem_euclid(86400);
        let str = format!(
            "{:04}{:02}{:02}{:02}{:02}{:02}Z",
            y,
            m,
            d,
            s / 3600,
            (s % 3600) / 60,
            s % 60
        );
        tlv(0x18, str.as_bytes())
    }

    /// A minimal but structurally valid X.509 DER whose `validity` is
    /// `(not_before, not_after)` — enough for `parse_validity` to walk to and
    /// read the two times. The signature/keys are placeholders (the sweep only
    /// reads validity; it never verifies the leaf's signature).
    fn mk_cert_der(not_before: i64, not_after: i64) -> Vec<u8> {
        let ecdsa_sha256 = tlv(
            0x30,
            &tlv(0x06, &[0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x04, 0x03, 0x02]),
        );
        let mut validity_c = gtime(not_before);
        validity_c.extend(gtime(not_after));
        let validity = tlv(0x30, &validity_c);
        // spki: AlgorithmIdentifier(ecPublicKey) + a stub BIT STRING.
        let spki = tlv(
            0x30,
            &[
                tlv(
                    0x30,
                    &tlv(0x06, &[0x2A, 0x86, 0x48, 0xCE, 0x3D, 0x02, 0x01]),
                ),
                tlv(0x03, &[0x00, 0x04]),
            ]
            .concat(),
        );
        let tbs_c = [
            tlv(0xA0, &tlv(0x02, &[0x02])), // [0] version = v3
            tlv(0x02, &[0x01]),             // serialNumber
            ecdsa_sha256.clone(),           // signature alg
            tlv(0x30, &[]),                 // issuer (empty Name)
            validity,
            tlv(0x30, &[]), // subject (empty Name)
            spki,
        ]
        .concat();
        let tbs = tlv(0x30, &tbs_c);
        let cert_c = [tbs, ecdsa_sha256, tlv(0x03, &[0x00])].concat();
        tlv(0x30, &cert_c)
    }

    #[test]
    fn mk_cert_roundtrips_through_parse_validity() {
        let nb = days_from_civil(2025, 1, 1) * 86400;
        let na = days_from_civil(2025, 4, 1) * 86400 + 12 * 3600;
        assert_eq!(parse_validity(&mk_cert_der(nb, na)), Some((nb, na)));
    }

    /// The GATE: seed a near-expiry leaf in the on-demand cache, run the sweep,
    /// and show it detects the leaf and re-mints it (the fresh leaf replaces the
    /// old one on disk) — plus the per-SNI rate limit stops a second re-mint.
    #[cfg(unix)]
    #[test]
    fn sweep_reissues_near_expiry_leaf_and_rate_limits() {
        use std::os::unix::fs::PermissionsExt;

        let base = std::env::temp_dir().join(format!(
            "drorb-sweep-demo-{}-{}",
            std::process::id(),
            unix_now()
        ));
        let cache = base.join("cache");
        let sni = "idle.apps.example.test";
        let snidir = cache.join(sni);
        std::fs::create_dir_all(&snidir).unwrap();

        let now = unix_now();
        // 90-day lifetime with only 5 days remaining ⇒ < 1/3 ⇒ due.
        let seed = mk_cert_der(now - 85 * 86400, now + 5 * 86400);
        std::fs::write(snidir.join("ecdsa-cert.der"), &seed).unwrap();
        std::fs::write(snidir.join("ecdsa-key.bin"), vec![0u8; 32]).unwrap();
        // Sanity: the seed really is due.
        let (snb, sna) = parse_validity(&seed).unwrap();
        assert!(due(now, snb, sna, 1.0 / 3.0), "seed leaf must read as due");

        // A stub `acme-issue` standing in for the CA transport (the ACME lane's
        // residual): it writes a fresh 1-year leaf into its $4 outdir and counts
        // its own invocations, so we can prove both the re-mint AND the rate limit.
        let fresh = mk_cert_der(now, now + 365 * 86400);
        let fresh_path = base.join("fresh.der");
        std::fs::write(&fresh_path, &fresh).unwrap();
        let counter = base.join("mint-count");
        let stub = base.join("stub-acme-issue.sh");
        std::fs::write(
            &stub,
            format!(
                "#!/bin/sh\nprintf 'x\\n' >> '{c}'\ncp '{f}' \"$4/ecdsa-cert.der\"\nhead -c 32 /dev/zero > \"$4/ecdsa-key.bin\"\n",
                c = counter.display(),
                f = fresh_path.display()
            ),
        )
        .unwrap();
        std::fs::set_permissions(&stub, std::fs::Permissions::from_mode(0o755)).unwrap();

        let cfg = SweepCfg {
            dir_url: "http://acme.test/dir".to_string(),
            cache_dir: cache.to_string_lossy().into_owned(),
            webroot: base.join("webroot").to_string_lossy().into_owned(),
            issue_bin: stub.to_string_lossy().into_owned(),
            contact: None,
            account_key: None,
            fraction: 1.0 / 3.0,
            min_reattempt: 3600,
        };

        let mut last_attempt: HashMap<String, i64> = HashMap::new();

        // First sweep: detects the near-expiry leaf and re-mints it.
        sweep(&cfg, now, &mut last_attempt, false);
        let after = std::fs::read(snidir.join("ecdsa-cert.der")).unwrap();
        let (_, na_after) = parse_validity(&after).unwrap();
        assert!(
            na_after >= now + 364 * 86400,
            "leaf must be re-minted to ~1yr; got notAfter now+{}d",
            (na_after - now) / 86400
        );
        assert_eq!(
            std::fs::read_to_string(&counter).unwrap().lines().count(),
            1,
            "exactly one CA order for the one due leaf"
        );

        // Second sweep, immediately, FORCED: the rate limit must still block a
        // second order for the same SNI (do not hammer the CA).
        sweep(&cfg, now, &mut last_attempt, true);
        assert_eq!(
            std::fs::read_to_string(&counter).unwrap().lines().count(),
            1,
            "rate limit must prevent a second re-mint within min_reattempt even under force"
        );

        // After the cooldown elapses, a forced sweep may re-mint again.
        sweep(&cfg, now + 3601, &mut last_attempt, true);
        assert_eq!(
            std::fs::read_to_string(&counter).unwrap().lines().count(),
            2,
            "past min_reattempt, a re-mint is allowed again"
        );

        std::fs::remove_dir_all(&base).ok();
    }

    /// A leaf with ample lifetime is left untouched (no needless CA order).
    #[cfg(unix)]
    #[test]
    fn sweep_skips_fresh_leaf() {
        let base = std::env::temp_dir().join(format!(
            "drorb-sweep-fresh-{}-{}",
            std::process::id(),
            unix_now()
        ));
        let cache = base.join("cache");
        let snidir = cache.join("busy.apps.example.test");
        std::fs::create_dir_all(&snidir).unwrap();
        let now = unix_now();
        // 90-day lifetime, 80 days remaining ⇒ not due.
        let fresh = mk_cert_der(now - 10 * 86400, now + 80 * 86400);
        std::fs::write(snidir.join("ecdsa-cert.der"), &fresh).unwrap();

        let cfg = SweepCfg {
            dir_url: "http://acme.test/dir".to_string(),
            cache_dir: cache.to_string_lossy().into_owned(),
            webroot: base.join("webroot").to_string_lossy().into_owned(),
            issue_bin: "/bin/false".to_string(), // must never be invoked
            contact: None,
            account_key: None,
            fraction: 1.0 / 3.0,
            min_reattempt: 3600,
        };
        let mut last_attempt: HashMap<String, i64> = HashMap::new();
        // force=false: a non-due leaf must not be re-minted (issuer would fail).
        sweep(&cfg, now, &mut last_attempt, false);
        assert!(
            last_attempt.is_empty(),
            "no re-mint attempt for a fresh leaf"
        );
        std::fs::remove_dir_all(&base).ok();
    }
}
