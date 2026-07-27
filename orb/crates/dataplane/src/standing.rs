//! Per-source STANDING counters for the reactor accept path — the state the
//! sans-IO serve fold structurally cannot carry.
//!
//! The proven serve stages `Reactor.Stage.ConnLimit` / `StickTable` / `Slowloris`
//! decide on PER-SOURCE STANDING state (how many connections a source has open
//! right now, its aggregated request rate, how long its header phase has run). The
//! serve fold is one stateless `ByteArray -> ByteArray` call per request
//! (`ctxOfMetered` supplies only the client IP + a per-connection sequence number),
//! so that standing state cannot ride the fold: it lives in the ACCEPT PATH, which
//! owns the connection lifecycle. This module is that store.
//!
//! ## ONE store per PROCESS — not one per shard
//!
//! `Reactor/StandingCounters.lean` models this store as a SINGLE map
//! `St := Ip -> Nat`, and `conn_conservation` reads
//! `s ip + #close(ip) = #accept(ip)` over the WHOLE accept/close history. The
//! quantity the proven `Reactor.Stage.ConnLimit.admits` decides on is therefore
//! the source's count across the whole reactor. There is exactly one such store
//! here — [`source_table`] — and every reactor backend (io_uring, kqueue,
//! blocking) uses it.
//!
//! This was not always so, and the divergence was a live product bug. The shard
//! reactors used to keep a lock-free per-SHARD counter table, one instance per
//! event-loop thread. Accepts from one source spread across shards, so a
//! configured `max-connections N` admitted about `N * shards` process-wide
//! (measured on a 24-core host: a cap of 4 served 94 of 200 concurrent
//! connections from one source), while the portable blocking host — the only
//! backend the DoS battery had ever been pointed at — enforced N exactly. The
//! Lean statement is per-source and stays per-source; the deployment was moved
//! onto it. See `conformance/dos/FINDING-per-shard-standing.md`.
//!
//! ## The cost of being right
//!
//! A process-wide bound on a per-core-sharded reactor cannot be maintained
//! without shared state: a shard that only sees its own accepts cannot know the
//! source's process-wide count. [`SharedStanding`] therefore takes one striped
//! mutex per accept, per close, and per request (the fold's `conn-active` feed).
//! The table is striped [`STRIPES`] ways by a hash of the source IP, so distinct
//! sources contend only on a collision; a single-source flood — the case the gate
//! exists for — serializes on one stripe by construction, which is the price of
//! counting it correctly.
//!
//! ## The accept/close discipline (decrement-exactly-once)
//!
//! The counter is incremented EXACTLY ONCE per connection that enters the
//! reactor and decremented EXACTLY ONCE when it leaves, so
//! `active(ip) = #accepted(ip) - #closed(ip)` and never goes negative — the
//! invariant proven in `Reactor/StandingCounters.lean` (`conn_conservation`,
//! `close_le_accept`). A counter leak (a missing decrement) would wedge the
//! limiter permanently, so the once-each discipline is load-bearing.
//!
//! Two callers, two shapes of the `accept` edge, both sound refinements:
//!
//! * [`SharedStanding::admit_counted`] — the SHARD reactors, which reach it through
//!   [`SharedStanding::enter_counted`] (the process-wide hard ceiling, then this).
//!   A refused connection
//!   still enters the shard's slab (io_uring/kqueue accepts complete after the
//!   handshake, so the shard owns the socket, writes a real `503`/`429` there and
//!   tears it down through the single close funnel). The `accept` edge is
//!   therefore "entered the slab", the counter is incremented whether or not the
//!   gate admitted, and `s ip` is the number of this source's connections
//!   currently IN the reactor.
//! * [`SharedStanding::admit`] — the BLOCKING host, whose refusals are written and
//!   dropped without ever spawning a worker. Its `accept` edge is "admitted", and
//!   a refusal is not counted.
//!
//! Both evaluate the same proven `admits` rule against the same process-wide
//! store; they differ only in whether an in-flight refusal is part of `s ip`.
//!
//! ## The TOTAL is a projection of the same store, not a second counter
//!
//! Two things need the number of connections currently in the process, not just
//! per source: the operator gauge (`/admin/connections`, `drorb_active_connections`)
//! and the process-wide HARD ceiling ([`process_conn_cap`]). Both read
//! [`SharedStanding::total_active`], which is maintained in the SAME operations that
//! maintain the per-source counters, so
//!
//! ```text
//!     total_active() == sum over ip of active(ip)
//! ```
//!
//! holds by construction (`total_is_the_sum_of_the_per_source_counters` asserts it).
//! It is deliberately NOT a third bookkeeping site: a separate counter with its own
//! increment/decrement calls is exactly the shape that drifts, and the gauge it feeds
//! was wrong for that reason — `crate::ACTIVE_CONNS` is incremented only by the
//! blocking host's accept loop, so on the shipped shard reactors `/admin/connections`
//! reported a PERMANENT ZERO while the process served.

use std::collections::HashMap;
use std::net::IpAddr;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

/// A per-source REQUEST-RATE window: how many request arrivals from this source have
/// landed since the window opened, and when it opened. The window is a fixed span
/// (`rate-window`) that AGES — once the span elapses the window is reset (`start`
/// advanced, `count` zeroed), so a source that pauses recovers and the counter never
/// leaks. This is the standing state the reactor consults against the `rate-limit`
/// cap; the proven decision (`Reactor.Stage.StickTable.admits` / `resp429`) decides.
struct RateWindow {
    /// When the current window opened (the last reset instant).
    start: Instant,
    /// Request arrivals counted in the current (unelapsed) window.
    count: u32,
}

/// **The slowloris expiry decision** — mirrors `Reactor.Stage.Slowloris.expired`:
/// with protection enabled (`timeout != 0`) a header phase that began at `started`
/// is expired at `now` iff the elapsed span has reached the timeout
/// (`now - started >= timeout`). A zero `timeout` disables the gate (never expires).
/// Total; the reactor drops an expired connection with the proven `resp408`.
///
/// Per-CONNECTION state (the header start instant rides the connection), so unlike
/// the counters below it needs no shared table and was never shard-split.
pub fn header_expired(timeout: Duration, started: Instant, now: Instant) -> bool {
    !timeout.is_zero() && now.duration_since(started) >= timeout
}

/// **THE process-wide per-source standing store.** One table for the whole reactor
/// process, whatever `--io` backend it runs and however many shards that backend
/// spawns — the single `St := Ip -> Nat` of `Reactor/StandingCounters.lean`.
///
/// Every backend must go through this accessor. A backend that keeps its own
/// instance re-creates the per-shard-standing bug: the configured cap is then
/// enforced once per instance rather than once per source.
pub fn source_table() -> &'static SharedStanding {
    static TABLE: std::sync::OnceLock<SharedStanding> = std::sync::OnceLock::new();
    TABLE.get_or_init(SharedStanding::new)
}

/// **The ceiling on the process-wide connection cap**, and the structural per-shard
/// slab bound the shard reactors are built with.
///
/// The two are ONE number on purpose. The shard reactors also carry a per-shard slab
/// bound (`MAX_CONNS_PER_SHARD`); if that bound were smaller than the process cap it
/// would bind first at low shard counts and the stated process bound would be a lie
/// at `--shards 1` and true at `--shards 24`. Setting them equal makes the per-shard
/// bound unreachable — a shard can only fill its slab past this if the process
/// already holds this many connections, which [`process_conn_cap`] refuses — so the
/// effective bound is `process_conn_cap()` for EVERY shard count.
///
/// 32768 is half the default `RLIMIT_NOFILE` this binary applies
/// (`DEFAULT_MAX_FDS` = 65536), leaving the other half for upstream proxy sockets,
/// static-file descriptors, pipes, listeners and the TLS/UDP paths.
pub const MAX_CONNS_CEILING: usize = 32_768;

/// The live process-wide connection ceiling. `0` = disabled (no process cap).
/// Set once at startup by `apply_resource_limits`; [`MAX_CONNS_CEILING`] until then
/// (so a unit test or an embedder that never calls the setter still has a bound).
static PROCESS_CONN_CAP: AtomicUsize = AtomicUsize::new(MAX_CONNS_CEILING);

/// **The process-wide HARD ceiling on simultaneously-open connections** — the
/// resource bound, distinct from the per-source `max-connections` policy gate.
///
/// Read on the accept path of every backend. `0` disables it. This is a bound on the
/// PROCESS, not on a shard: the shard reactors used to enforce `MAX_CONNS_PER_SHARD`
/// (16384) per event loop, which on a 24-core host is a ceiling of 393,216 —
/// the same per-shard-vs-process-wide shape as the per-source gate this module
/// already had to fix, in the hard cap. See `conformance/dos/FINDING-per-shard-standing.md`.
pub fn process_conn_cap() -> usize {
    PROCESS_CONN_CAP.load(Ordering::Relaxed)
}

/// Install the process-wide connection ceiling. Called once from
/// `main::apply_resource_limits`, which knows the `RLIMIT_NOFILE` soft limit it just
/// applied; see [`derive_process_conn_cap`].
pub fn set_process_conn_cap(cap: usize) {
    PROCESS_CONN_CAP.store(cap, Ordering::Relaxed);
}

/// **Derive the process-wide connection ceiling** from the descriptor budget the
/// process actually has, so the two cannot drift: a connection costs at least one
/// descriptor, so a connection ceiling above `RLIMIT_NOFILE` is not a ceiling at all
/// — accept fails with `EMFILE` first and the "cap" never fires. That was the state
/// of the tree: `MAX_CONNS_PER_SHARD * shards` = 393,216 against a 65,536 fd budget,
/// while `DEFAULT_MAX_FDS`'s doc comment claimed to be "well above the connection
/// ceilings so the reactor's own caps bind first".
///
/// * An explicit `DRORB_MAX_CONNS` wins outright (including `0` = disabled), so an
///   operator can state the bound and a test can exercise it at a small value.
/// * Otherwise: HALF the applied fd soft limit, capped at [`MAX_CONNS_CEILING`] and
///   floored at 256. Half, because a connection is not the only descriptor a
///   reverse-proxy hop needs (an upstream socket, a static-file fd, a splice pipe).
///   `fd_soft == 0` (unknown) falls back to the ceiling.
pub fn derive_process_conn_cap(fd_soft: u64) -> usize {
    if let Ok(v) = std::env::var("DRORB_MAX_CONNS") {
        if let Ok(n) = v.parse::<usize>() {
            return n;
        }
    }
    if fd_soft == 0 {
        return MAX_CONNS_CEILING;
    }
    ((fd_soft / 2) as usize).clamp(256, MAX_CONNS_CEILING)
}

/// Connections dropped at the process-wide ceiling. NOT exposed on `/metrics`: the
/// exposed family fleet is stated byte-for-byte by `Admin/MetricsFormat.lean`
/// (`deployedRegistry`, `baselineMetricsText`) and adding a `reason` there without
/// extending the Lean would widen a drift this tree already has (the Lean fleet is
/// missing `reason="body_limit"`, which Rust emits). Read by
/// [`process_cap_refusals`] and announced on stderr the first time it fires.
static PROCESS_CAP_REFUSALS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// How many arrivals the process-wide ceiling has dropped since start.
pub fn process_cap_refusals() -> u64 {
    PROCESS_CAP_REFUSALS.load(Ordering::Relaxed)
}

/// The outcome of a SHARD reactor's accept-path admission
/// ([`SharedStanding::enter_counted`]). Three outcomes, because the two refusals owe
/// the caller different things.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Admission {
    /// Under the per-source cap: dispatch to the serve. Counted; owes one `on_close`.
    Admitted,
    /// At/over the per-source `max-connections` cap: write the proven `503`. The
    /// connection IS in the slab and IS counted, so it owes one `on_close` — the
    /// uniform close funnel the shard reactors depend on.
    OverSourceCap,
    /// The PROCESS-WIDE hard ceiling ([`process_conn_cap`]) is full. NOTHING was
    /// counted and NO `on_close` is owed: the caller closes the descriptor without
    /// entering it in the slab. This is a resource refusal, not a policy decision,
    /// and it is deliberately silent on the wire (no response is written) — at the
    /// ceiling the cheapest possible disposal is the point.
    AtProcessCap,
}

/// RAII decrement for a connection whose ownership LEAVES the shard: the WebSocket,
/// CONNECT, h2c and reverse-proxy handoffs move the descriptor to a dedicated thread
/// and drop the slab entry, but the connection is still open and still belongs to its
/// source. Moving one of these into the spawned thread keeps the source counted for
/// the connection's whole life and releases it exactly once when the thread returns —
/// including on an unwinding panic.
///
/// The handoffs used to call `on_close` AT HANDOFF, which made `max-connections N`
/// unenforceable against exactly the long-lived connection shapes: an upgraded
/// WebSocket or a CONNECT tunnel stopped counting against its source's cap the
/// instant it became long-lived. The blocking host never had that hole (its
/// `ConnCountGuard` lives for the whole worker), so it is one more divergence of the
/// shape `FINDING-per-shard-standing.md` names.
pub struct ConnGuard {
    ip: IpAddr,
}

impl ConnGuard {
    /// Take ownership of one already-counted connection's decrement.
    pub fn new(ip: IpAddr) -> Self {
        ConnGuard { ip }
    }
}

impl Drop for ConnGuard {
    fn drop(&mut self) {
        source_table().on_close(self.ip);
    }
}

/// The process-wide per-source counter table, shared by every reactor backend and
/// (on the shard reactors) by every shard thread.
///
/// Sharded into [`STRIPES`] independent buckets keyed by a hash of the source IP, so
/// two different sources almost never contend and there is NO single global mutex
/// on the accept path — the contention on any one stripe is `1/STRIPES` of the
/// source population.
pub struct SharedStanding {
    stripes: Vec<std::sync::Mutex<HashMap<IpAddr, u32>>>,
    /// Striped per-source CONNECTION-arrival windows, for the accept path's
    /// `rate-limit`/`429` gate — the fixed-sliding-window discipline of
    /// `Reactor.Stage.StickTable`, striped so concurrent accepts from different
    /// sources rarely contend.
    rate_stripes: Vec<std::sync::Mutex<HashMap<IpAddr, RateWindow>>>,
    /// Striped per-source REQUEST-arrival windows — the reading the PROVEN fold gate
    /// decides on ([`SharedStanding::req_note_prior`]).
    ///
    /// WHY A SECOND WINDOW AND NOT THE ONE ABOVE. The accept path counts CONNECTION
    /// arrivals: it runs once per `accept()`, so on a kept-alive connection requests
    /// 2..N are never counted by it at all, and a single connection issuing ten
    /// thousand requests passes its gate untouched. That is a real hole in the
    /// per-source request-rate bound the `rate-limit` directive names, and it is the
    /// hole the fold gate closes — which it can only do if it is fed a count of
    /// REQUESTS. Folding requests into the accept window instead would have changed
    /// what the accept gate measures (every connection would consume two of its
    /// budget), silently retuning a shipped gate; two windows over the same configured
    /// `limit`/`window` keeps each gate's own bound exactly what it was.
    req_stripes: Vec<std::sync::Mutex<HashMap<IpAddr, RateWindow>>>,
    /// **The sum of every per-source counter**, maintained in the same operations
    /// that maintain them (see the module header). Feeds the operator gauge and the
    /// process-wide hard ceiling; it is a projection of this store, never an
    /// independent count.
    total: AtomicUsize,
    /// Per-PROCESS random key for stripe selection (see [`SharedStanding::stripe_idx`]).
    seed: u64,
}

/// Stripe count. Sized for the SHARD reactors: every one of `shards` event loops
/// now reaches this table on every accept and every request, so the stripe count
/// has to exceed the thread count by a wide margin or the table serializes them.
/// Measured on hbox (24 cores, 16 concurrent writers, 4096 distinct sources, in a
/// tight loop with no reactor work in between — an upper bound on contention, not
/// the deployed rate): 64 stripes cost 1074 ns per accept+close pair, 1024 cost
/// 747, 4096 cost 603 but regressed the uncontended single-thread case (cache
/// footprint). Must be a power of two.
const STRIPES: usize = 1024;
const STRIPE_BITS: u32 = STRIPES.trailing_zeros();

impl Default for SharedStanding {
    fn default() -> Self {
        Self::new()
    }
}

impl SharedStanding {
    pub fn new() -> Self {
        let stripes = (0..STRIPES)
            .map(|_| std::sync::Mutex::new(HashMap::new()))
            .collect();
        let rate_stripes = (0..STRIPES)
            .map(|_| std::sync::Mutex::new(HashMap::new()))
            .collect();
        let req_stripes = (0..STRIPES)
            .map(|_| std::sync::Mutex::new(HashMap::new()))
            .collect();
        // A per-process random key, from the same OS-seeded source the standard
        // library's `HashMap` uses for its own keys.
        let seed = {
            use std::hash::{BuildHasher, Hasher};
            std::collections::hash_map::RandomState::new()
                .build_hasher()
                .finish()
        };
        SharedStanding {
            stripes,
            rate_stripes,
            req_stripes,
            total: AtomicUsize::new(0),
            seed,
        }
    }

    /// Which stripe a source falls in: fold the address to 64 bits, mix with this
    /// table's per-process key, and take the TOP [`STRIPE_BITS`] bits of a
    /// multiply by the golden-ratio constant (Fibonacci hashing — multiplication
    /// mixes low bits upward, so the high bits depend on the whole input).
    ///
    /// Two deliberate changes from the `DefaultHasher` this used to call:
    ///
    /// * **Cheaper.** 1.6 ns against ~25 ns for SipHash, on a path that every
    ///   accept AND every request now takes.
    /// * **KEYED.** `DefaultHasher::new()` is SipHash-1-3 with FIXED zero keys, so
    ///   the stripe an address landed in was fully predictable and an attacker with
    ///   an address pool could aim a distributed flood at a single stripe and
    ///   serialize the table. The per-process `seed` removes that; it is not a MAC,
    ///   but an attacker who cannot see the key cannot choose colliding addresses.
    ///
    /// Spread is asserted by `stripe_mix_spreads_a_flat_address_range` — a
    /// degenerate mix would quietly reintroduce the contention the stripes exist
    /// to remove, which is not the kind of thing to leave to inspection.
    #[inline]
    fn stripe_idx(&self, ip: IpAddr) -> usize {
        let folded: u64 = match ip {
            IpAddr::V4(a) => u32::from_be_bytes(a.octets()) as u64,
            IpAddr::V6(a) => {
                let o = a.octets();
                u64::from_be_bytes(o[0..8].try_into().unwrap())
                    ^ u64::from_be_bytes(o[8..16].try_into().unwrap())
            }
        };
        ((folded ^ self.seed).wrapping_mul(0x9e37_79b9_7f4a_7c15) >> (64 - STRIPE_BITS)) as usize
    }

    fn stripe(&self, ip: IpAddr) -> &std::sync::Mutex<HashMap<IpAddr, u32>> {
        &self.stripes[self.stripe_idx(ip)]
    }

    fn rate_stripe(&self, ip: IpAddr) -> &std::sync::Mutex<HashMap<IpAddr, RateWindow>> {
        &self.rate_stripes[self.stripe_idx(ip)]
    }

    fn req_stripe(&self, ip: IpAddr) -> &std::sync::Mutex<HashMap<IpAddr, RateWindow>> {
        &self.req_stripes[self.stripe_idx(ip)]
    }

    /// Age a fixed sliding window, count one arrival in it, and return the count that
    /// was there BEFORE this arrival. One critical section, so concurrent arrivals from
    /// one source cannot both age the window and lose each other's count.
    ///
    /// Returning the PRIOR count (not the post-increment one) is what makes this a
    /// *counting read* the proven gate can decide on directly: it is the same shape as
    /// the connection reading (`active` excludes the connection being admitted), so the
    /// fold applies one rule — `Reactor.Stage.StickTable.admitsAt limit prior` — and
    /// exactly `limit` arrivals per window are admitted.
    fn note_window(
        map: &std::sync::Mutex<HashMap<IpAddr, RateWindow>>,
        ip: IpAddr,
        window: Duration,
        now: Instant,
    ) -> u32 {
        let mut g = map.lock().unwrap();
        let w = g.entry(ip).or_insert(RateWindow {
            start: now,
            count: 0,
        });
        if now.duration_since(w.start) >= window {
            w.start = now;
            w.count = 0;
        }
        let prior = w.count;
        w.count = w.count.saturating_add(1);
        prior
    }

    /// **THE COUNTING READ the proven fold gate decides on.** Note one REQUEST arrival
    /// from `ip` against the source's request window and return how many were already
    /// counted in it — the number the host threads to
    /// `Reactor.Stage.StickTable.countOf`, where `admitsAt limit count` answers the
    /// `429`.
    ///
    /// This exists because [`SharedStanding::rate_note`] returns a `bool`: it makes the
    /// DECISION in Rust and discards the quantity, so the proven gate had nothing to
    /// read and was dead code. Rust's job here is to produce the number; the fold's job
    /// is to decide. Nothing on this path compares `prior` to `limit`.
    ///
    /// `limit == 0` (the gate disabled) returns `0` and takes NO lock — the fold reads
    /// a `0` limit as unlimited, so there is nothing to count and no reason to pay for
    /// it on the request hot path.
    pub fn req_note_prior(&self, ip: IpAddr, limit: u32, window: Duration, now: Instant) -> u32 {
        if limit == 0 {
            return 0;
        }
        Self::note_window(self.req_stripe(ip), ip, window, now)
    }

    /// The source's current in-window REQUEST count, without noting an arrival. For
    /// tests / introspection.
    pub fn req_count(&self, ip: IpAddr, window: Duration, now: Instant) -> u32 {
        let g = self.req_stripe(ip).lock().unwrap();
        match g.get(&ip) {
            Some(w) if now.duration_since(w.start) < window => w.count,
            _ => 0,
        }
    }

    /// Note a request arrival from `ip` against the rate gate (striped, atomic per
    /// source). Ages the source's window, counts the arrival, and returns `true` iff
    /// it is OVER `limit` (refuse `429`). `limit == 0` disables the gate entirely
    /// (always `false`, no bookkeeping — the unlimited default, and no lock taken).
    /// The age-and-count is a SINGLE critical section, so concurrent arrivals from
    /// one source cannot both age the window and lose each other's count.
    pub fn rate_note(&self, ip: IpAddr, limit: u32, window: Duration, now: Instant) -> bool {
        if limit == 0 {
            return false;
        }
        // `note_window` returns the count BEFORE this arrival; the post-increment count
        // is `prior + 1`, and the accept gate refuses once that exceeds `limit` —
        // byte-for-byte the rule this function had before it shared the window helper.
        Self::note_window(self.rate_stripe(ip), ip, window, now) + 1 > limit
    }

    /// The source's current in-window arrival count (`0` for an unseen source, or one
    /// whose window has elapsed but not yet been re-noted). For tests / introspection.
    pub fn rate_count(&self, ip: IpAddr, window: Duration, now: Instant) -> u32 {
        let g = self.rate_stripe(ip).lock().unwrap();
        match g.get(&ip) {
            Some(w) if now.duration_since(w.start) < window => w.count,
            _ => 0,
        }
    }

    /// Reclaim rate-window entries whose window has fully elapsed by `now` — idle
    /// sources leave no residue, bounding the table to sources active within the last
    /// `window`. Without this the rate map is itself a memory-exhaustion vector: one
    /// packet per spoofed source would allocate an entry that never goes away.
    /// Called opportunistically off the shard reactor's periodic sweep, throttled to
    /// once per window; walks every stripe, taking them one at a time so it never
    /// holds more than one lock.
    pub fn rate_prune(&self, window: Duration, now: Instant) {
        for s in self.rate_stripes.iter().chain(self.req_stripes.iter()) {
            s.lock()
                .unwrap()
                .retain(|_, w| now.duration_since(w.start) < window);
        }
    }

    /// **The accept decision for a caller whose refusals never enter a slab** (the
    /// blocking host). Atomically read the source's active count and, iff it is
    /// under `cap` (or `cap == 0` = unlimited), increment and admit. Returns `true`
    /// when admitted; a refusal is NOT counted, so no matching `on_close` is owed.
    ///
    /// The check-and-increment is a single critical section so concurrent accepts
    /// from one source cannot both slip past the boundary (no TOCTOU over-admit) —
    /// the invariant modelled exhaustively under loom in `crates/conn-limit-twin`.
    pub fn admit(&self, ip: IpAddr, cap: u32) -> bool {
        let mut g = self.stripe(ip).lock().unwrap();
        let n = g.get(&ip).copied().unwrap_or(0);
        if cap != 0 && n >= cap {
            return false;
        }
        *g.entry(ip).or_insert(0) += 1;
        self.total.fetch_add(1, Ordering::Relaxed);
        true
    }

    /// **The accept decision for the SHARD reactors**, where a refused connection
    /// still enters the slab and exits through the same close funnel as a served
    /// one. Reads the source's process-wide count, applies the proven admission rule
    /// (`Reactor.Stage.ConnLimit.admits`: `cap == 0` = unlimited, else admit iff the
    /// count is strictly under `cap`), and counts this connection — all in ONE
    /// critical section.
    ///
    /// The single critical section is what makes this correct across shards: with a
    /// separate read and increment, `shards` event loops accepting the same source
    /// concurrently could all read the same under-cap value and all admit,
    /// over-admitting by up to `shards - 1`. That race did not exist while the
    /// counters were shard-local (one thread each) and appears the instant they are
    /// shared, so it is closed here rather than left to chance.
    ///
    /// The increment happens whether or not the gate admitted: on these reactors the
    /// `accept` edge of `Reactor/StandingCounters.lean` is "entered the slab", and
    /// every connection in the slab decrements exactly once at `close`. So the close
    /// funnel stays uniform — no per-connection "was it counted" flag to get wrong,
    /// which is the failure mode (`close_le_accept`) that would wedge the gate.
    pub fn admit_counted(&self, ip: IpAddr, cap: u32) -> bool {
        self.total.fetch_add(1, Ordering::Relaxed);
        self.count_source(ip, cap)
    }

    /// The per-source half of the shard reactors' accept decision: read the source's
    /// process-wide count, apply the proven `admits` rule, and count this connection
    /// — in ONE critical section (see [`SharedStanding::admit_counted`] for why the
    /// single section is load-bearing). Does NOT touch [`SharedStanding::total`];
    /// its callers own that, because the hard-cap reservation has to happen before
    /// the per-source work.
    fn count_source(&self, ip: IpAddr, cap: u32) -> bool {
        let mut g = self.stripe(ip).lock().unwrap();
        let n = g.entry(ip).or_insert(0);
        let admitted = cap == 0 || *n < cap;
        *n = n.saturating_add(1);
        admitted
    }

    /// **The shard reactors' full accept decision: the process-wide HARD ceiling
    /// first, then the per-source policy gate.**
    ///
    /// `hard` bounds the connections this PROCESS may hold at once
    /// ([`process_conn_cap`]); `0` disables it. The reservation is a single
    /// `fetch_update` on the total, so the ceiling is EXACT under concurrent accepts
    /// on every shard — a plain read-then-increment would let `shards` event loops
    /// each see the same under-cap total and each admit, overshooting by up to
    /// `shards - 1`. That is the same race `admit_counted`'s single critical section
    /// closes for the per-source gate, and it appears here for the same reason.
    ///
    /// On [`Admission::AtProcessCap`] nothing is counted and no `on_close` is owed;
    /// on the other two outcomes the connection is counted exactly once and owes
    /// exactly one `on_close`.
    ///
    /// Ordering: the ceiling is a RESOURCE bound and is checked first, so a process
    /// that is genuinely full disposes of the arrival for the price of one atomic —
    /// no stripe lock, no slab entry, no response. The per-source `503` is a policy
    /// answer and is worth a real response; it only runs when the process has room.
    pub fn enter_counted(&self, ip: IpAddr, cap: u32, hard: usize) -> Admission {
        if self
            .total
            .fetch_update(Ordering::AcqRel, Ordering::Acquire, |n| {
                if hard != 0 && n >= hard {
                    None
                } else {
                    Some(n + 1)
                }
            })
            .is_err()
        {
            PROCESS_CAP_REFUSALS.fetch_add(1, Ordering::Relaxed);
            // Announce ONCE. A process sitting at its connection ceiling is a state
            // an operator has to be able to learn about, and this refusal writes
            // nothing on the wire (at the ceiling, the cheapest disposal is the
            // point) — so without this line it is invisible.
            static ANNOUNCED: std::sync::Once = std::sync::Once::new();
            ANNOUNCED.call_once(|| {
                eprintln!(
                    "dataplane: PROCESS-WIDE connection ceiling ({hard}) reached — \
                     dropping arrivals until connections close. This is a process \
                     bound across all shards; raise it with DRORB_MAX_CONNS (and the \
                     descriptor budget with DRORB_MAX_FDS). Logged once."
                );
            });
            return Admission::AtProcessCap;
        }
        if self.count_source(ip, cap) {
            Admission::Admitted
        } else {
            Admission::OverSourceCap
        }
    }

    /// **The number of connections currently in the process**, across every source
    /// and every shard — the sum of the per-source counters, maintained by the same
    /// accept/close discipline (see the module header). This is what
    /// `/admin/connections` and `drorb_active_connections` report.
    pub fn total_active(&self) -> usize {
        self.total.load(Ordering::Relaxed)
    }

    /// Decrement the source's active count (drops the entry at zero, so a flood that
    /// opens and closes leaves no residue). Called exactly once per connection that
    /// was counted at accept. Saturating at zero as defence in depth — the
    /// accept/close discipline keeps it exact, but a stray decrement can never wrap
    /// below zero and wedge the gate.
    pub fn on_close(&self, ip: IpAddr) {
        let mut g = self.stripe(ip).lock().unwrap();
        let decremented = match g.get_mut(&ip) {
            Some(n) => {
                *n = n.saturating_sub(1);
                if *n == 0 {
                    g.remove(&ip);
                }
                true
            }
            // A close with no matching accept: the source is already at zero, so
            // there is nothing to decrement — and the TOTAL must not move either, or
            // it would drift below the sum of the per-source counters.
            None => false,
        };
        drop(g);
        if decremented {
            // Saturating as defence in depth, exactly as the per-source counter: the
            // discipline keeps this exact, and a stray decrement can never wrap.
            let _ = self
                .total
                .fetch_update(Ordering::AcqRel, Ordering::Acquire, |n| {
                    Some(n.saturating_sub(1))
                });
        }
    }

    /// The source's current active-connection count INCLUDING this connection (which
    /// the accept gate already incremented). Read on the serve path to feed the
    /// proven `Reactor.Stage.ConnLimit` fold gate the source's standing load; the
    /// caller subtracts one to obtain the count of OTHER concurrent connections. `0`
    /// for an unseen source.
    pub fn active(&self, ip: IpAddr) -> u32 {
        let g = self.stripe(ip).lock().unwrap();
        g.get(&ip).copied().unwrap_or(0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::net::Ipv4Addr;

    fn ip(a: u8) -> IpAddr {
        IpAddr::V4(Ipv4Addr::new(10, 0, 0, a))
    }

    #[test]
    fn accept_close_is_conserved() {
        let s = SharedStanding::new();
        assert_eq!(s.active(ip(1)), 0);
        // Open four from one source; a fifth would see active == 4.
        for _ in 0..4 {
            assert!(s.admit_counted(ip(1), 0));
        }
        assert_eq!(s.active(ip(1)), 4);
        // A different source is independent (per-source, not global).
        assert!(s.admit_counted(ip(2), 0));
        assert_eq!(s.active(ip(2)), 1);
        assert_eq!(s.active(ip(1)), 4);
        // Close them all — the counter returns to zero (no leak) and the entry
        // is reclaimed.
        for _ in 0..4 {
            s.on_close(ip(1));
        }
        assert_eq!(s.active(ip(1)), 0);
    }

    #[test]
    fn decrement_never_underflows() {
        let s = SharedStanding::new();
        // A close with no matching accept is a no-op, never a wrap.
        s.on_close(ip(9));
        assert_eq!(s.active(ip(9)), 0);
    }

    #[test]
    fn open_close_repeatedly_no_residue() {
        let s = SharedStanding::new();
        for _ in 0..1000 {
            assert!(s.admit_counted(ip(7), 0));
            s.on_close(ip(7));
        }
        assert_eq!(s.active(ip(7)), 0);
    }

    /// The shard-reactor gate: the proven `admits` truth table, and the fact that a
    /// refused connection IS counted (it is in the slab) so its close is owed.
    #[test]
    fn admit_counted_matches_the_proven_rule() {
        let s = SharedStanding::new();
        // Under the cap: admitted (`admits_under`).
        assert!(s.admit_counted(ip(1), 4));
        assert!(s.admit_counted(ip(1), 4));
        assert!(s.admit_counted(ip(1), 4));
        assert!(s.admit_counted(ip(1), 4));
        assert_eq!(s.active(ip(1)), 4);
        // At the cap: refused (`admits_at_cap`) — and still counted, because the
        // refused connection is in the slab until its 503 drains.
        assert!(!s.admit_counted(ip(1), 4));
        assert_eq!(s.active(ip(1)), 5);
        // Over the cap: still refused (`admits_over`).
        assert!(!s.admit_counted(ip(1), 4));
        // Every one of the six owes exactly one close; after them the source is clean.
        for _ in 0..6 {
            s.on_close(ip(1));
        }
        assert_eq!(s.active(ip(1)), 0);
        // A disabled cap admits any load (`admits_unlimited`).
        for _ in 0..100 {
            assert!(s.admit_counted(ip(2), 0));
        }
    }

    /// THE REGRESSION for `conformance/dos/FINDING-per-shard-standing.md`: the cap is
    /// enforced once per SOURCE across every thread that accepts, not once per
    /// accepting thread. With a per-shard table this admitted `cap * threads`.
    #[test]
    fn cap_is_process_wide_across_concurrent_accepters() {
        use std::sync::Arc;
        use std::sync::atomic::{AtomicU32, Ordering};
        let s = Arc::new(SharedStanding::new());
        let admitted = Arc::new(AtomicU32::new(0));
        let cap = 4u32;
        let threads: Vec<_> = (0..24)
            .map(|_| {
                let s = Arc::clone(&s);
                let admitted = Arc::clone(&admitted);
                std::thread::spawn(move || {
                    for _ in 0..50 {
                        if s.admit_counted(ip(5), cap) {
                            admitted.fetch_add(1, Ordering::Relaxed);
                        }
                    }
                })
            })
            .collect();
        for t in threads {
            t.join().unwrap();
        }
        // Nothing ever closed, so at most `cap` of the 1200 attempts may be admitted
        // — EXACTLY cap, and not `cap * 24`, which is what the per-shard tables gave.
        assert_eq!(admitted.load(Ordering::Relaxed), cap);
    }

    /// THE REGRESSION for the gauge that reported a permanent zero: the total is a
    /// PROJECTION of the per-source store, so it equals the sum of the per-source
    /// counters after every mix of admits, refusals and closes — on the shard-reactor
    /// edge (`admit_counted`, refusals counted) and the blocking edge (`admit`,
    /// refusals not counted) alike. A separate counter with its own call sites is
    /// what drifted; this asserts there is nothing to drift.
    #[test]
    fn total_is_the_sum_of_the_per_source_counters() {
        let s = SharedStanding::new();
        let sum = |s: &SharedStanding| -> usize {
            s.stripes
                .iter()
                .map(|st| {
                    st.lock()
                        .unwrap()
                        .values()
                        .map(|&v| v as usize)
                        .sum::<usize>()
                })
                .sum()
        };
        assert_eq!(s.total_active(), 0);
        // Shard-reactor edge: four under a cap of 3 — three admitted, one refused,
        // ALL FOUR counted (a refusal is in the slab).
        for _ in 0..4 {
            s.admit_counted(ip(1), 3);
        }
        assert_eq!(s.total_active(), 4);
        // Blocking edge: three under a cap of 2 — two admitted and counted, one
        // refused and NOT counted.
        for _ in 0..3 {
            s.admit(ip(2), 2);
        }
        assert_eq!(s.total_active(), 6);
        assert_eq!(sum(&s), s.total_active());
        // A stray close for an unseen source moves neither.
        s.on_close(ip(9));
        assert_eq!(s.total_active(), 6);
        assert_eq!(sum(&s), s.total_active());
        // Every owed close: back to zero, no residue in either.
        for _ in 0..4 {
            s.on_close(ip(1));
        }
        for _ in 0..2 {
            s.on_close(ip(2));
        }
        assert_eq!(s.total_active(), 0);
        assert_eq!(sum(&s), 0);
    }

    /// The PROCESS-WIDE hard ceiling is exact, and it is checked BEFORE the
    /// per-source gate: a refusal at the ceiling counts nothing and owes no close.
    #[test]
    fn process_ceiling_is_exact_and_owes_no_close() {
        let s = SharedStanding::new();
        // Ten distinct sources, an unlimited per-source cap, a process ceiling of 6.
        let outcomes: Vec<Admission> = (0..10).map(|i| s.enter_counted(ip(i), 0, 6)).collect();
        assert_eq!(
            outcomes
                .iter()
                .filter(|a| **a == Admission::Admitted)
                .count(),
            6
        );
        assert!(outcomes[6..].iter().all(|a| *a == Admission::AtProcessCap));
        assert_eq!(s.total_active(), 6);
        // The refused sources were never counted at all.
        assert_eq!(s.active(ip(7)), 0);
        // Closing one admitted connection frees exactly one slot.
        s.on_close(ip(0));
        assert_eq!(s.enter_counted(ip(7), 0, 6), Admission::Admitted);
        assert_eq!(s.enter_counted(ip(8), 0, 6), Admission::AtProcessCap);
        // `hard == 0` disables the ceiling.
        for i in 20..40u8 {
            assert_eq!(s.enter_counted(ip(i), 0, 0), Admission::Admitted);
        }
    }

    /// The ceiling holds across CONCURRENT accepters — the shard-reactor case. A
    /// read-then-increment would let each of the 24 threads see the same under-cap
    /// total and admit, overshooting by up to 23.
    #[test]
    fn process_ceiling_is_exact_under_concurrent_accepters() {
        use std::sync::Arc;
        use std::sync::atomic::AtomicU32;
        let s = Arc::new(SharedStanding::new());
        let admitted = Arc::new(AtomicU32::new(0));
        let hard = 100usize;
        let threads: Vec<_> = (0..24)
            .map(|t| {
                let s = Arc::clone(&s);
                let admitted = Arc::clone(&admitted);
                std::thread::spawn(move || {
                    for i in 0..50 {
                        // Distinct sources, so the per-source cap never binds and the
                        // ONLY bound under test is the process ceiling.
                        let a = s.enter_counted(ip((t * 50 + i) as u8), 0, hard);
                        if a != Admission::AtProcessCap {
                            admitted.fetch_add(1, Ordering::Relaxed);
                        }
                    }
                })
            })
            .collect();
        for t in threads {
            t.join().unwrap();
        }
        assert_eq!(admitted.load(Ordering::Relaxed) as usize, hard);
        assert_eq!(s.total_active(), hard);
    }

    /// The handoff guard decrements exactly once, when the thread that owns the
    /// long-lived connection returns — and on a panic in it, which is the whole
    /// reason it is RAII rather than a call at the end.
    #[test]
    fn conn_guard_decrements_once_including_on_panic() {
        let t = source_table();
        let base = t.active(ip(200));
        t.admit_counted(ip(200), 0);
        assert_eq!(t.active(ip(200)), base + 1);
        {
            let _g = ConnGuard::new(ip(200));
        }
        assert_eq!(t.active(ip(200)), base);
        // The panicking path: the guard's Drop runs while unwinding.
        t.admit_counted(ip(200), 0);
        let r = std::panic::catch_unwind(|| {
            let _g = ConnGuard::new(ip(200));
            panic!("the handoff thread died");
        });
        assert!(r.is_err());
        assert_eq!(t.active(ip(200)), base);
    }

    /// `DRORB_MAX_CONNS` wins outright; otherwise the ceiling is derived from the
    /// descriptor budget so a "cap" above `RLIMIT_NOFILE` — which is what the tree
    /// shipped — cannot be stated.
    #[test]
    fn process_conn_cap_is_derived_from_the_fd_budget() {
        // The default fd soft limit this binary applies.
        assert_eq!(derive_process_conn_cap(65_536), 32_768);
        // A small budget: half of it, and never above the ceiling.
        assert_eq!(derive_process_conn_cap(4_096), 2_048);
        assert_eq!(derive_process_conn_cap(1_048_576), MAX_CONNS_CEILING);
        // A tiny/unknown budget still leaves a workable floor.
        assert_eq!(derive_process_conn_cap(16), 256);
        assert_eq!(derive_process_conn_cap(0), MAX_CONNS_CEILING);
        // What the tree shipped: 16384 per shard x 24 shards is 393,216, six times
        // the descriptor budget it runs under — the cap could not bind before EMFILE.
        assert!(16_384 * 24 > 65_536);
        assert!(derive_process_conn_cap(65_536) < 65_536);
    }

    #[test]
    fn rate_window_admits_then_429s_then_recovers() {
        let s = SharedStanding::new();
        let t0 = Instant::now();
        let win = Duration::from_secs(10);
        let limit = 3u32;
        // The first `limit` arrivals are under the cap (not over).
        assert!(!s.rate_note(ip(1), limit, win, t0)); // count 1
        assert!(!s.rate_note(ip(1), limit, win, t0)); // 2
        assert!(!s.rate_note(ip(1), limit, win, t0)); // 3
        assert_eq!(s.rate_count(ip(1), win, t0), 3);
        // The 4th (and further) arrivals WITHIN the window are over the cap → 429.
        assert!(s.rate_note(ip(1), limit, win, t0)); // 4 > 3

        // The REQUEST window is INDEPENDENT of the connection window: noting requests
        // must not consume the accept gate's budget (that would silently retune a
        // shipped gate), and vice versa.
        let t = SharedStanding::new();
        assert_eq!(t.req_note_prior(ip(2), limit, win, t0), 0);
        assert_eq!(t.req_note_prior(ip(2), limit, win, t0), 1);
        assert_eq!(t.req_note_prior(ip(2), limit, win, t0), 2);
        assert_eq!(t.req_count(ip(2), win, t0), 3);
        // …and the connection window for the same source has seen nothing.
        assert_eq!(t.rate_count(ip(2), win, t0), 0);
        // A disabled limit takes no lock, counts nothing, and reads back 0 — the fold
        // reads a 0 limit as unlimited, so there is nothing to count.
        assert_eq!(t.req_note_prior(ip(3), 0, win, t0), 0);
        assert_eq!(t.req_count(ip(3), win, t0), 0);
        // The window AGES: past its width the prior count is 0 again (no leak).
        assert_eq!(t.req_note_prior(ip(2), limit, win, t0 + win + win), 0);
        assert!(s.rate_note(ip(1), limit, win, t0)); // 5 > 3
        // A different source is independent (per-source, not global).
        assert!(!s.rate_note(ip(2), limit, win, t0));
        // After the window fully elapses the window AGES: the source is counted from
        // zero again and is served (recovery — no leak).
        let t1 = t0 + Duration::from_secs(11);
        assert_eq!(s.rate_count(ip(1), win, t1), 0);
        assert!(!s.rate_note(ip(1), limit, win, t1)); // fresh window, count 1
    }

    #[test]
    fn rate_disabled_never_fires() {
        let s = SharedStanding::new();
        let t0 = Instant::now();
        // limit 0 = unlimited: never over, and it records no state.
        for _ in 0..1000 {
            assert!(!s.rate_note(ip(3), 0, Duration::from_secs(1), t0));
        }
        assert_eq!(s.rate_count(ip(3), Duration::from_secs(1), t0), 0);
    }

    /// The rate limiter is likewise process-wide: a burst spread over many accepting
    /// threads is counted against ONE window, so `rate-limit N` admits N, not
    /// `N * threads`.
    #[test]
    fn rate_limit_is_process_wide_across_concurrent_accepters() {
        use std::sync::Arc;
        use std::sync::atomic::{AtomicU32, Ordering};
        let s = Arc::new(SharedStanding::new());
        let served = Arc::new(AtomicU32::new(0));
        let win = Duration::from_secs(600); // never ages during the test
        let t0 = Instant::now();
        let limit = 8u32;
        let threads: Vec<_> = (0..24)
            .map(|_| {
                let s = Arc::clone(&s);
                let served = Arc::clone(&served);
                std::thread::spawn(move || {
                    for _ in 0..50 {
                        if !s.rate_note(ip(6), limit, win, t0) {
                            served.fetch_add(1, Ordering::Relaxed);
                        }
                    }
                })
            })
            .collect();
        for t in threads {
            t.join().unwrap();
        }
        assert_eq!(served.load(Ordering::Relaxed), limit);
    }

    #[test]
    fn rate_prune_reclaims_idle_sources() {
        let s = SharedStanding::new();
        let t0 = Instant::now();
        let win = Duration::from_secs(5);
        s.rate_note(ip(4), 10, win, t0);
        s.rate_note(ip(5), 10, win, t0);
        assert_eq!(s.rate_count(ip(4), win, t0), 1);
        assert_eq!(s.rate_count(ip(5), win, t0), 1);
        // Well past the window: both entries are idle and reclaimed from every stripe.
        let t1 = t0 + Duration::from_secs(6);
        s.rate_prune(win, t1);
        let total: usize = s
            .rate_stripes
            .iter()
            .map(|st| st.lock().unwrap().len())
            .sum();
        assert_eq!(total, 0);
    }

    /// The stripe mix must actually SPREAD. A degenerate one (say, the low octet)
    /// would funnel a whole subnet onto a handful of stripes and serialize the
    /// table — silently undoing the striping, with every test above still green.
    /// Checked on three shapes an operator really sees: a flat contiguous range, a
    /// host per /24 across many subnets, and scattered addresses.
    #[test]
    fn stripe_mix_spreads_every_address_shape() {
        use std::collections::HashSet;
        let s = SharedStanding::new();
        let distinct = |v: Vec<IpAddr>| -> usize {
            v.into_iter()
                .map(|ip| s.stripe_idx(ip))
                .collect::<HashSet<_>>()
                .len()
        };
        let v4 = |x: u32| IpAddr::V4(Ipv4Addr::from(x));
        // 4096 addresses over 1024 stripes: the coupon-collector expectation is
        // 1024 * (1 - e^-4) ~= 1006 distinct stripes. Under 950 means collapsing.
        let flat = distinct((0..4096).map(|i| v4(0x0a00_0000 | i)).collect());
        let per_24 = distinct((0..4096).map(|i| v4(0x0a00_0000 | (i << 8) | 1)).collect());
        let scattered = distinct(
            (0..4096u32)
                .map(|i| v4(i.wrapping_mul(2_654_435_761)))
                .collect(),
        );
        for (name, got) in [
            ("flat", flat),
            ("per-/24", per_24),
            ("scattered", scattered),
        ] {
            assert!(
                got > 950,
                "stripe mix degenerate on {name}: {got} distinct stripes for 4096 \
                 addresses (expected ~1006 of {STRIPES})"
            );
        }
        // Every index is in range.
        assert!((0..4096).all(|i| s.stripe_idx(v4(i)) < STRIPES));
    }

    /// The stripe key is per-PROCESS, not a compile-time constant: two tables
    /// disagree about where a source lands, so an attacker cannot precompute a set
    /// of addresses that collide on one stripe.
    #[test]
    fn stripe_key_is_not_fixed() {
        let a = SharedStanding::new();
        let b = SharedStanding::new();
        assert_ne!(a.seed, b.seed);
        let disagreements = (0..256u32)
            .filter(|&i| {
                let ip = IpAddr::V4(Ipv4Addr::from(0x0a00_0000 | i));
                a.stripe_idx(ip) != b.stripe_idx(ip)
            })
            .count();
        // Two independent keys agree on ~1/1024 of addresses by chance.
        assert!(
            disagreements > 240,
            "keys look correlated: {disagreements}/256"
        );
    }

    #[test]
    fn header_expired_matches_the_proven_rule() {
        let started = Instant::now();
        let timeout = Duration::from_millis(100);
        // In time: not expired.
        assert!(!header_expired(timeout, started, started));
        assert!(!header_expired(
            timeout,
            started,
            started + Duration::from_millis(50)
        ));
        // At/over the deadline: expired.
        assert!(header_expired(timeout, started, started + timeout));
        assert!(header_expired(
            timeout,
            started,
            started + Duration::from_millis(200)
        ));
        // Disabled (zero timeout): never expires.
        assert!(!header_expired(
            Duration::ZERO,
            started,
            started + Duration::from_secs(3600)
        ));
    }
}
