// PORTED dregg-native from the prior operated layer (verbatim; the
// DnsResolver trait and its re-exports match at this crate's root).
//
// WIRING (main loop): in `src/lib.rs` add — ideally behind a `live-dns` feature so
// the crate stays dependency-light by default —
//     #[cfg(feature = "live-dns")] pub mod live;
//     #[cfg(feature = "live-dns")] pub use live::LiveDns;
// and in `Cargo.toml`:
//     [features] live-dns = ["dep:hickory-resolver", "dep:tokio"]
//     hickory-resolver = { version = "0.25", default-features = false, features = ["system-config", "tokio"], optional = true }
//     tokio = { version = "1", default-features = false, features = ["rt", "net", "time"], optional = true }
//! The production [`DnsResolver`]: real TXT / CNAME lookups over a live DNS client.
//!
//! Where [`MockDns`](crate::MockDns) is the deterministic test instance of the
//! [`DnsResolver`] trait seam, [`LiveDns`] is the instance that actually queries the
//! network — so a real domain owner who publishes the `_dregg-verify.<domain>` TXT
//! (or the `<domain>` CNAME) gets their [`DomainBinding`](crate::DomainBinding)
//! flipped to [`Verified`](crate::VerificationState::Verified) against *live* DNS.
//! It is the instance the production verify path uses; tests keep [`MockDns`].
//!
//! ## Sync trait over an async client
//!
//! The [`DnsResolver`] trait is synchronous (the bind → verify state machine and the
//! gateway routing are sync), while the underlying DNS client
//! ([`hickory_resolver`]) is async, and its `Resolver` is neither `Send` nor `Sync`
//! — its lookup futures cannot cross threads. So [`LiveDns`] **pins** one resolver +
//! a single-threaded Tokio runtime to one dedicated worker thread and talks to it
//! over channels: a trait call sends the name (a `Send` `String`) and blocks on the
//! reply (a `Send` `Vec<String>` / `Option<String>`). This is correct regardless of
//! the caller's context — it never calls `block_on` on a thread that already owns a
//! runtime, so it cannot panic with "cannot block the current thread from within a
//! runtime".
//!
//! ## Edge cases (the real-DNS realities)
//!
//! - **NXDOMAIN / no records / timeout** → an empty answer ([`Vec::new`] / [`None`]).
//!   The verify check reads "no proof", never an error, never a false-positive — an
//!   unreachable resolver leaves a binding [`Pending`](crate::VerificationState::Pending),
//!   it never mints a cert nor routes a byte.
//! - **Multiple TXT records** → all are returned; the verify check accepts iff *any*
//!   carries the nonce. A single multi-segment TXT record's character-strings are
//!   concatenated (the canonical TXT value).
//! - **Stale negatives** → the resolver is configured to **not cache** (`cache_size =
//!   0`, zero negative TTL), so an owner who publishes the record and immediately
//!   re-verifies is not defeated by a cached "not found". Verify is on-demand; a
//!   fresh wire query each time is the correct trade.

use std::sync::mpsc::{self, Sender};
use std::time::Duration;

use hickory_resolver::TokioResolver;
use hickory_resolver::config::{ResolverConfig, ResolverOpts};
use hickory_resolver::name_server::TokioConnectionProvider;
use hickory_resolver::proto::rr::{RData, RecordType};

use crate::DnsResolver;

/// The per-lookup wire timeout and retry budget — a verify is interactive (an owner
/// is waiting on `dregg domains verify`), so fail fast rather than hang.
const LOOKUP_TIMEOUT: Duration = Duration::from_secs(5);
const LOOKUP_ATTEMPTS: usize = 2;

/// A lookup request handed to the resolver worker thread, carrying its reply channel.
enum Job {
    Txt {
        name: String,
        reply: Sender<Vec<String>>,
    },
    Cname {
        name: String,
        reply: Sender<Option<String>>,
    },
}

/// A live [`DnsResolver`] backed by [`hickory_resolver`] — the production verify
/// path's resolver. Real TXT/CNAME lookups against live DNS.
///
/// Construct once and share by clone (cheap — it holds a channel to the resolver
/// worker thread); each [`DnsResolver`] call is a fresh (uncached) wire query. Built
/// from the system resolver configuration (`/etc/resolv.conf` / the Windows
/// registry), falling back to Cloudflare (1.1.1.1) if that cannot be read.
#[derive(Clone)]
pub struct LiveDns {
    jobs: Sender<Job>,
}

impl LiveDns {
    /// Build a live resolver from the system DNS configuration (Cloudflare fallback).
    ///
    /// Spawns the dedicated resolver worker thread (a single-threaded Tokio runtime +
    /// the pinned `Resolver`). Returns an error only if that runtime cannot be
    /// created; a missing/unreadable system config is *not* fatal — it falls back to
    /// Cloudflare.
    pub fn from_system() -> std::io::Result<LiveDns> {
        let (jobs, rx) = mpsc::channel::<Job>();
        let (ready_tx, ready_rx) = mpsc::channel::<std::io::Result<()>>();

        std::thread::Builder::new()
            .name("dregg-domains-dns".to_string())
            .spawn(move || {
                // The resolver and its futures are !Send/!Sync; everything DNS lives
                // and dies on this one thread.
                let runtime = match tokio::runtime::Builder::new_current_thread()
                    .enable_all()
                    .build()
                {
                    Ok(rt) => rt,
                    Err(e) => {
                        let _ = ready_tx.send(Err(e));
                        return;
                    }
                };
                // Build inside the runtime context so the async DNS client can find
                // its reactor handle.
                let resolver = {
                    let _guard = runtime.enter();
                    build_resolver()
                };
                let _ = ready_tx.send(Ok(()));

                // The resolver's connection provider uses `spawn_local`, so lookups
                // must run inside a `LocalSet`. Serve them until every `LiveDns`
                // handle is dropped (the channel closes), one at a time — verify is
                // low-volume.
                let local = tokio::task::LocalSet::new();
                for job in rx {
                    match job {
                        Job::Txt { name, reply } => {
                            let v = local.block_on(&runtime, lookup_txt(&resolver, &name));
                            let _ = reply.send(v);
                        }
                        Job::Cname { name, reply } => {
                            let v = local.block_on(&runtime, lookup_cname(&resolver, &name));
                            let _ = reply.send(v);
                        }
                    }
                }
            })?;

        match ready_rx.recv() {
            Ok(Ok(())) => Ok(LiveDns { jobs }),
            Ok(Err(e)) => Err(e),
            Err(_) => Err(std::io::Error::other("DNS resolver worker failed to start")),
        }
    }
}

/// Build the pinned resolver: system config, Cloudflare fallback, no caching.
fn build_resolver() -> TokioResolver {
    // Prefer the system resolver configuration; fall back to Cloudflare (1.1.1.1)
    // when it is missing or carries no nameservers. The empty-nameserver fallback is
    // load-bearing on macOS, where `/etc/resolv.conf` is a stub that parses to a
    // config with zero servers (which would silently fail every lookup).
    let config = hickory_resolver::system_conf::read_system_conf()
        .ok()
        .map(|(config, _opts)| config)
        .filter(|config| !config.name_servers().is_empty())
        .unwrap_or_else(ResolverConfig::cloudflare);
    let mut builder =
        TokioResolver::builder_with_config(config, TokioConnectionProvider::default());
    {
        let opts: &mut ResolverOpts = builder.options_mut();
        opts.timeout = LOOKUP_TIMEOUT;
        opts.attempts = LOOKUP_ATTEMPTS;
        // Retry over TCP when a UDP answer is truncated or dropped — robust against
        // resolvers/middleboxes that mishandle large UDP DNS responses.
        opts.try_tcp_on_error = true;
        // Verify is on-demand: never trust a cached (especially negative) answer, or
        // an owner who just published the record could be told it is missing.
        opts.cache_size = 0;
        opts.negative_min_ttl = Some(Duration::ZERO);
        opts.negative_max_ttl = Some(Duration::ZERO);
    }
    builder.build()
}

/// A verification name is always absolute — query it as an FQDN (trailing dot) so no
/// resolver search domain (e.g. macOS's `local`) is ever appended.
fn fqdn(name: &str) -> String {
    format!("{}.", name.trim_end_matches('.'))
}

/// One TXT lookup. NXDOMAIN / no records / timeout → no records (not an error).
async fn lookup_txt(resolver: &TokioResolver, name: &str) -> Vec<String> {
    match resolver.txt_lookup(fqdn(name)).await {
        Ok(lookup) => lookup
            .iter()
            .map(|txt| {
                // A TXT record is one or more character-strings; its value is their
                // concatenation (a long nonce may be split at 255 bytes).
                let mut bytes = Vec::new();
                for seg in txt.txt_data() {
                    bytes.extend_from_slice(seg);
                }
                String::from_utf8_lossy(&bytes).into_owned()
            })
            .collect(),
        Err(_) => Vec::new(),
    }
}

/// One CNAME lookup. The target carries a trailing dot (FQDN form); the verify check
/// compares case-insensitively without it.
async fn lookup_cname(resolver: &TokioResolver, name: &str) -> Option<String> {
    match resolver.lookup(fqdn(name), RecordType::CNAME).await {
        Ok(lookup) => lookup.iter().find_map(|rdata| match rdata {
            RData::CNAME(cname) => Some(cname.0.to_string()),
            _ => None,
        }),
        Err(_) => None,
    }
}

impl DnsResolver for LiveDns {
    fn txt(&self, name: &str) -> Vec<String> {
        let (reply, rx) = mpsc::channel();
        if self
            .jobs
            .send(Job::Txt {
                name: name.to_string(),
                reply,
            })
            .is_err()
        {
            return Vec::new();
        }
        rx.recv().unwrap_or_default()
    }

    fn cname(&self, name: &str) -> Option<String> {
        let (reply, rx) = mpsc::channel();
        if self
            .jobs
            .send(Job::Cname {
                name: name.to_string(),
                reply,
            })
            .is_err()
        {
            return None;
        }
        rx.recv().unwrap_or(None)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The live resolver builds (worker thread + runtime + resolver) and is usable
    /// through the [`DnsResolver`] trait object — the production default compiles and
    /// wires. No network: construction reads no records.
    #[test]
    fn live_resolver_builds_and_is_a_dns_resolver() {
        let live = LiveDns::from_system().expect("build live resolver");
        let _dyn: &dyn DnsResolver = &live;
    }

    /// A real lookup against public DNS. Ignored by default (needs network); run with
    /// `cargo test -p starbridge-domains --features live-dns -- --ignored` on a connected host.
    #[test]
    #[ignore = "requires live network DNS"]
    fn live_lookup_real_domain() {
        let live = LiveDns::from_system().expect("build");
        // example.com publishes TXT records (and is stable for tests).
        let some = live.txt("example.com");
        assert!(
            !some.is_empty(),
            "expected some TXT records for example.com"
        );
        // A real CNAME resolves (trailing-dot FQDN form, which verify strips).
        assert!(
            live.cname("www.github.com").is_some(),
            "www.github.com is a CNAME"
        );
        // A guaranteed-nonexistent name must yield no records (not an error).
        let none = live.txt("_dregg-verify.nonexistent-995ab.invalid");
        assert!(none.is_empty(), "NXDOMAIN must yield no records");
    }
}
