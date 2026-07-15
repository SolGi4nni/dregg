//! The macOS / BSD IO path: a per-core kqueue completion-queue reactor.
//!
//! This is the preferred IO path on macOS and the BSDs, the sibling of the Linux
//! `io_uring` loop (`uring`). It replaces the thread-per-connection blocking model
//! with a small number of **shards** — one single-threaded event loop per core —
//! each driving its own `kqueue` over its own connection set. Like the io_uring
//! shards this is the share-nothing reactor model: no connection state, buffer, or
//! slab is shared between shards.
//!
//! ## Accept distribution across shards
//!
//! Each shard binds its own listener with `SO_REUSEPORT` (`SO_REUSEADDR` too), the
//! kernel-load-balancing primitive on Linux and FreeBSD (`SO_REUSEPORT_LB`).
//! Darwin's `SO_REUSEPORT`, however, only *permits* the duplicate binds — it does
//! not hash-distribute connections, delivering every accept to a single socket. So
//! the reactor does not rely on the kernel to pick a shard: every shard registers
//! *all* the shards' listeners on its own kqueue, level-triggered, and the shards
//! race `accept()`. Whichever listener the kernel queues a connection on, all the
//! shards see it and one wins the accept — a portable per-shard load balancer that
//! distributes on Darwin and the BSDs alike, and composes with `SO_REUSEPORT`
//! hashing where the kernel provides it. A small per-turn accept batch keeps one
//! shard from draining a whole burst before its siblings get a turn.
//!
//! ## Readiness turned into completions
//!
//! `kqueue` is a *readiness* interface, not a completion one: it reports that an
//! fd can be read or written, not that bytes have moved. This reactor presents the
//! same **completion** surface the io_uring shards do by doing the I/O inline at
//! the point readiness is known:
//!
//!   - **Inline fast path.** `want_read` / `want_write` attempt the `recv` / `send`
//!     syscall immediately (`MSG_DONTWAIT`). On success the bytes are in hand and
//!     the request is framed / the response advanced synchronously — the kqueue is
//!     never touched. Only on `EAGAIN` is the corresponding filter (`EVFILT_READ`
//!     for recv, `EVFILT_WRITE` for send) registered `EV_ADD|EV_CLEAR`, deferring
//!     the work to the next readiness edge.
//!   - **One kevent per turn.** The poll makes a single `kevent` call that both
//!     flushes the batched registration changelist and waits for the next edges;
//!     each ready fd then does its inline I/O and produces its completion. The work
//!     per turn is `O(ready)`, not `O(registered)`.
//!   - **Adaptive backoff.** A saturated socket that returns `EAGAIN` in a streak
//!     would burn one syscall per optimistic inline attempt; after a streak the
//!     reactor skips the next `2^streak` inline attempts (capped) for that
//!     direction and waits on the filter instead, resetting on the first success.
//!
//! ## The one shared resource, and where the ceiling is
//!
//! Exactly as with the io_uring shards: the proven core is a pure
//! `ByteArray -> ByteArray` transform, so a shard needs no shared mutable engine
//! state to run it, but the Lean runtime is a process-global singleton. Every
//! shard funnels its framed requests to the one runtime-owner thread over the
//! serve gateway and is woken with the response through its own self-pipe. The IO
//! fabric scales across shard cores; the serve transform does not, so the
//! steady-state ceiling is `1 / (serve latency)` however many shards feed it.
//!
//! ## Confinement
//!
//! A shard's reactor, its slab, and every buffer live and die on the one shard
//! thread; nothing here is `Sync`. The single cross-thread entry is [`wake`],
//! called by the runtime-owner thread when a response is waiting in a shard's
//! mailbox — it writes one byte to that shard's self-pipe, whose read end is
//! registered on the kqueue, breaking the `kevent` wait.

use std::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr, ToSocketAddrs};
use std::os::fd::{FromRawFd, RawFd};
use std::sync::atomic::Ordering;
use std::sync::mpsc::{Receiver, Sender, channel};
use std::time::Instant;

use libc::{c_int, c_void, sa_family_t, socklen_t};

use crate::http::{
    Frame, H2_PREFACE, annotate_connection, next_request, request_wants_keepalive,
    response_is_self_delimited,
};
use crate::pool::PooledBuf;
use crate::serve::{KqDone, Meter, ServeGateway, ServeReply};

/// Bytes offered to the kernel per receive.
const RECV_CHUNK: usize = 16384;
/// Events reaped per `kevent` call.
const EVENT_CAP: usize = 1024;
/// Cap on live connections per shard; new accepts beyond it are closed. This is
/// also the bound on outstanding read ops (one per connection).
const MAX_CONNS_PER_SHARD: usize = 16384;
/// Cap on the per-direction inline-skip exponent, so the adaptive backoff never
/// skips more than `2^BACKOFF_MAX` inline attempts before waiting on the filter.
const BACKOFF_MAX: u32 = 6;
/// Connections a shard accepts per readiness turn before yielding. The listener
/// filters are level-triggered, so a burst larger than this re-fires next turn
/// and a sibling shard gets a chance to win the race — spreading accepts.
const ACCEPT_BATCH: u32 = 32;
/// How long the reactor blocks in one `kevent` before checking the shutdown flag.
const POLL_TIMEOUT: libc::timespec = libc::timespec {
    tv_sec: 0,
    tv_nsec: 200_000_000, // 200ms
};

// udata sentinels distinguishing the listener and the self-pipe from connection
// slots. A connection carries its slab slot as `udata`; direction comes from the
// event's filter (EVFILT_READ vs EVFILT_WRITE). Slots are `u32`, so they never
// reach these top-of-range sentinels.
const UD_WAKE: usize = usize::MAX;
const UD_LISTENER: usize = usize::MAX - 1;

/// Signal a shard that a serve response is waiting in its mailbox, by writing one
/// byte to its self-pipe. Called from the runtime-owner serve thread; the byte
/// makes the shard's read end readable and breaks its `kevent` wait.
pub fn wake(pipe_wr: RawFd) {
    let one: u8 = 1;
    // SAFETY: a 1-byte write to the write end of a live pipe owned by the target
    // shard for the process lifetime. The write cannot block meaningfully (a pipe
    // buffer holds far more than the in-flight wakeup count) and a full pipe only
    // means a wakeup is already pending, so a dropped byte is harmless.
    unsafe {
        libc::write(pipe_wr, &one as *const u8 as *const c_void, 1);
    }
}

/// Per-connection state owned by a single shard. No field is shared across
/// shards; a `Conn` and its buffers live and die on one shard thread.
struct Conn {
    fd: RawFd,
    /// The accept peer's IP — the default client address the metered IP-filter
    /// gate decides on (overridden by a forwarded client when the peer is a
    /// trusted proxy; see `blocking::client_addr`). Captured from the accept
    /// sockaddr.
    peer_ip: IpAddr,
    /// Per-connection request index, threaded as the rate bucket's standing
    /// depletion: request 0 sees a full bucket, later requests on the same
    /// kept-alive connection find it draining. Advances once per served request —
    /// the kqueue analogue of `blocking::handle_conn`'s `conn_seq`.
    conn_seq: u64,
    /// Accumulation buffer: recv fills it; framing consumes it.
    acc: PooledBuf,
    /// Response being written, and how many of its bytes are already out.
    resp: Option<PooledBuf>,
    sent: usize,
    /// The in-flight request's keep-alive intent (HTTP/1.1 framing).
    req_keepalive: bool,
    /// Whether this connection stays open after the in-flight response — the
    /// request's intent AND the response being self-delimited.
    keepalive: bool,
    /// h2c connections are served once then closed (no HTTP/1.1 keep-alive).
    h2c: bool,
    /// A framed request has been handed to the serve gateway and its response is
    /// not yet back; the reactor neither reads nor writes on this fd until then.
    serving: bool,
    /// `EVFILT_READ` is currently registered for this fd (avoids duplicate adds;
    /// the registration persists for the connection's life — closing the fd
    /// removes it from the kqueue).
    read_armed: bool,
    /// `EVFILT_WRITE` is currently registered (armed only while a partial send is
    /// draining, deleted once the response is fully out).
    write_armed: bool,
    /// Consecutive `EAGAIN` streak per direction, and the count of upcoming inline
    /// attempts to skip — the adaptive backoff.
    rd_streak: u32,
    rd_skip: u32,
    wr_streak: u32,
    wr_skip: u32,
    /// OBSERVABILITY: the per-request start instant, captured at dispatch (mirrors
    /// `blocking::handle_conn`'s `req_start`) and read when the response is staged for
    /// the access-log duration. Reset on each request of a kept-alive connection.
    req_start: Instant,
    /// OBSERVABILITY: the request line + effective client captured at dispatch, but
    /// only when the access log is enabled (`None` when off — nothing is parsed and the
    /// log is skipped). Consumed when the response is staged.
    logrec: Option<(crate::access_log::ReqLine, IpAddr)>,
    /// SLOWLORIS: when this connection's header phase began (captured at accept). The
    /// reactor drops it with a `408` if its FIRST request head has not completed
    /// within `slowloris-timeout` of this instant (`Reactor.Stage.Slowloris.expired`).
    hdr_start: Instant,
    /// SLOWLORIS: set true once the first request has been framed and dispatched — the
    /// header phase is over, so the slow-header gate no longer applies.
    headers_done: bool,
}

/// A free-list slab of connections (O(1) insert/remove, slot reuse). One per
/// shard — the same shape the io_uring shards use.
struct Slab {
    conns: Vec<Option<Conn>>,
    free: Vec<u32>,
}

impl Slab {
    fn new() -> Self {
        Slab {
            conns: Vec::new(),
            free: Vec::new(),
        }
    }
    fn live(&self) -> usize {
        self.conns.len() - self.free.len()
    }
    fn insert(&mut self, c: Conn) -> u32 {
        if let Some(i) = self.free.pop() {
            self.conns[i as usize] = Some(c);
            i
        } else {
            let i = self.conns.len() as u32;
            self.conns.push(Some(c));
            i
        }
    }
    fn get(&mut self, i: u32) -> Option<&mut Conn> {
        self.conns.get_mut(i as usize).and_then(|s| s.as_mut())
    }
    fn remove(&mut self, i: u32) {
        if let Some(slot) = self.conns.get_mut(i as usize) {
            if slot.take().is_some() {
                self.free.push(i);
            }
        }
    }
}

/// What a dispatch attempt on a connection's accumulation buffer resolved to.
enum Disp {
    /// A complete request was framed and handed to the serve gateway.
    Served,
    /// Not enough bytes buffered for a complete request; read more.
    NeedMore,
    /// The connection was closed (oversize request, or the serve thread is gone).
    Closed,
}

/// Everything a shard threads through its readiness handlers.
struct Reactor {
    /// This shard's 0-based index (used only for the optional accept trace).
    id: usize,
    /// Connections this shard has won the accept race for (the accept trace
    /// reports its first, evidence accepts are spreading across shards).
    accepted: u64,
    /// Whether the `DRORB_KQ_TRACE` accept trace is on (off by default).
    trace: bool,
    /// Self-pipe: `wake_wr` is written by the serve thread, `wake_rd` is
    /// registered on the kqueue so that write breaks the wait.
    wake_rd: RawFd,
    wake_wr: RawFd,
    gw: ServeGateway,
    /// The serve-completion mailbox: the serve thread posts finished responses
    /// here and wakes the reactor.
    mtx: Sender<KqDone>,
    mrx: Receiver<KqDone>,
    slab: Slab,
    /// Batched kqueue registration changes, flushed by the next `kevent`.
    changes: Vec<libc::kevent>,
    /// Per-source STANDING connection counters, shard-local (no lock): the
    /// accept-path state the sans-IO serve fold cannot carry. Incremented at accept,
    /// decremented at `close` — exactly once each — enforcing the config's
    /// `max-connections` cap (the proven `Reactor.Stage.ConnLimit` decision).
    standing: crate::standing::Standing,
}

/// The canned `503 Service Unavailable` a source at/over its `max-connections` cap
/// receives — the wire form of the proven `Reactor.Stage.ConnLimit.resp503`.
const CONN_LIMIT_503: &[u8] =
    b"HTTP/1.1 503 Service Unavailable\r\nContent-Type: text/plain\r\nContent-Length: 36\r\n\r\nper-source connection limit reached\n";

/// The canned `429 Too Many Requests` a source over its `rate-limit` window receives
/// — the wire form of the proven `Reactor.Stage.StickTable.resp429`.
const RATE_LIMIT_429: &[u8] =
    b"HTTP/1.1 429 Too Many Requests\r\nContent-Type: text/plain\r\nContent-Length: 20\r\n\r\nrate limit exceeded\n";

/// The canned `408 Request Timeout` a connection whose header phase overran
/// `slowloris-timeout` receives — the wire form of the proven
/// `Reactor.Stage.Slowloris.resp408`.
const SLOWLORIS_408: &[u8] =
    b"HTTP/1.1 408 Request Timeout\r\nContent-Type: text/plain\r\nContent-Length: 23\r\n\r\nrequest header timeout\n";

/// Run `shards` kqueue reactor threads, each binding its own `SO_REUSEPORT`
/// listener on `bind` so the kernel load-balances accepts across them, and
/// driving every request through `gw`. Blocks until every shard exits (on
/// shutdown).
pub fn run(bind: &str, gw: ServeGateway, shards: usize) {
    // A closed peer must never kill the process with SIGPIPE; the accepted
    // sockets also carry SO_NOSIGPIPE, but ignore it globally as belt-and-braces.
    // SAFETY: installing SIG_IGN for SIGPIPE is async-signal-safe and standard.
    unsafe {
        libc::signal(libc::SIGPIPE, libc::SIG_IGN);
    }

    let addr: SocketAddr = match bind.to_socket_addrs().ok().and_then(|mut a| a.next()) {
        Some(a) => a,
        None => {
            eprintln!("dataplane: kqueue reactor cannot resolve bind address {bind}");
            return;
        }
    };

    // One SO_REUSEPORT listener per shard. Every shard watches ALL of them and
    // races accept(), so accepts distribute across shards on every platform (see
    // the accept-distribution note above).
    let mut listeners: Vec<RawFd> = Vec::with_capacity(shards);
    for id in 0..shards {
        match bind_reuseport(addr) {
            Ok(fd) => listeners.push(fd),
            Err(e) => {
                eprintln!("dataplane: kqueue shard {id} listener bind failed: {e}");
                if id == 0 {
                    std::process::exit(1); // nothing to serve
                }
                break; // fewer shards than requested, but keep serving
            }
        }
    }

    let mut handles = Vec::new();
    for id in 0..listeners.len() {
        let listeners = listeners.clone(); // RawFd is Copy; each shard watches all
        let gw = gw.clone();
        handles.push(
            std::thread::Builder::new()
                .name(format!("drorb-kq-{id}"))
                .spawn(move || {
                    if let Err(e) = reactor_loop(listeners, gw, id) {
                        eprintln!("dataplane: kqueue shard {id} exited: {e}");
                    }
                })
                .expect("failed to spawn kqueue shard"),
        );
    }
    for h in handles {
        let _ = h.join();
    }
}

/// One shard: its own kqueue, self-pipe, connection slab, and serve mailbox. It
/// watches every shard's listener (`listeners`) and races accept with its
/// siblings.
fn reactor_loop(listeners: Vec<RawFd>, gw: ServeGateway, id: usize) -> std::io::Result<()> {
    // SAFETY: kqueue(2) returns a fresh kqueue descriptor owned by this shard for
    // its lifetime; the result is checked.
    let kq = unsafe { libc::kqueue() };
    if kq < 0 {
        return Err(std::io::Error::last_os_error());
    }

    // Self-pipe for serve-completion wakeups; both ends non-blocking.
    let mut fds = [0 as c_int; 2];
    // SAFETY: pipe(2) with a valid 2-element out array; the result is checked.
    if unsafe { libc::pipe(fds.as_mut_ptr()) } < 0 {
        return Err(std::io::Error::last_os_error());
    }
    let (wake_rd, wake_wr) = (fds[0], fds[1]);
    set_nonblocking(wake_rd);
    set_nonblocking(wake_wr);

    let (mtx, mrx): (Sender<KqDone>, Receiver<KqDone>) = channel();
    let mut r = Reactor {
        id,
        accepted: 0,
        trace: std::env::var_os("DRORB_KQ_TRACE").is_some(),
        wake_rd,
        wake_wr,
        gw,
        mtx,
        mrx,
        slab: Slab::new(),
        changes: Vec::new(),
        standing: crate::standing::Standing::new(),
    };

    // Register every shard's listener LEVEL-triggered (no EV_CLEAR): while any of
    // them has a pending connection this shard keeps being told, so it can race
    // its siblings for the accept without missing bursts. The accept handler reads
    // the ready fd from the event's `ident`.
    for &lfd in &listeners {
        r.changes.push(kev(
            lfd as usize,
            libc::EVFILT_READ,
            libc::EV_ADD,
            UD_LISTENER,
        ));
    }
    // The self-pipe read end is edge-triggered (drained on each wakeup).
    r.changes.push(kev(
        wake_rd as usize,
        libc::EVFILT_READ,
        libc::EV_ADD | libc::EV_CLEAR,
        UD_WAKE,
    ));

    let mut events: Vec<libc::kevent> = (0..EVENT_CAP).map(|_| empty_kevent()).collect();

    loop {
        if crate::SHUTDOWN.load(Ordering::SeqCst) {
            return Ok(());
        }

        // ONE kevent: flush the batched registration changelist AND wait for the
        // next readiness edges (up to the poll timeout, so shutdown is observed).
        // SAFETY: `changes` and `events` are valid, correctly-sized kevent arrays;
        // `kq` is this shard's live kqueue; the timeout is a valid timespec.
        let n = unsafe {
            libc::kevent(
                kq,
                r.changes.as_ptr(),
                r.changes.len() as c_int,
                events.as_mut_ptr(),
                EVENT_CAP as c_int,
                &POLL_TIMEOUT,
            )
        };
        r.changes.clear();

        if n < 0 {
            let e = std::io::Error::last_os_error();
            if e.raw_os_error() == Some(libc::EINTR) {
                continue;
            }
            return Err(e);
        }

        // Copy out (udata, filter, flags) so no borrow of `events` outlives the
        // handlers (which push new registration changes and mutate the slab).
        for i in 0..n as usize {
            let ev = &events[i];
            let ud = ev.udata as usize;
            let filter = ev.filter;
            let ident = ev.ident as RawFd;
            match ud {
                UD_WAKE => r.on_wakeup(),
                UD_LISTENER => r.on_accept_ready(ident),
                slot => {
                    let slot = slot as u32;
                    if filter == libc::EVFILT_WRITE {
                        r.on_writable(slot);
                    } else {
                        r.on_readable(slot);
                    }
                }
            }
        }
    }
}

impl Reactor {
    // --- readiness handlers ------------------------------------------------

    /// A listener (`lfd`, the ready fd from the event's `ident`) is readable:
    /// accept a bounded batch, driving each new connection straight into the
    /// inline read fast path. The batch cap yields to sibling shards on a burst;
    /// the level-triggered listener re-fires next turn if connections remain.
    fn on_accept_ready(&mut self, lfd: RawFd) {
        let mut taken = 0u32;
        loop {
            if taken >= ACCEPT_BATCH {
                return; // yield; the level-triggered listener re-fires if more wait
            }
            // SAFETY: accept(2) on the ready listener fd; the connecting peer's
            // address lands in the local `ss`/`slen` in/out pair (its client IP is
            // the metered gate's default decision address). The returned fd is
            // checked; `ss` is only read on a successful accept.
            let mut ss: libc::sockaddr_storage = unsafe { std::mem::zeroed() };
            let mut slen = std::mem::size_of::<libc::sockaddr_storage>() as socklen_t;
            let fd = unsafe {
                libc::accept(
                    lfd,
                    &mut ss as *mut libc::sockaddr_storage as *mut libc::sockaddr,
                    &mut slen,
                )
            };
            if fd < 0 {
                let e = std::io::Error::last_os_error();
                match e.raw_os_error() {
                    // (EWOULDBLOCK == EAGAIN): drained, or a sibling won the race.
                    Some(libc::EAGAIN) => return,
                    Some(libc::EINTR) => continue,
                    _ => return, // transient accept error; the next turn retries
                }
            }
            taken += 1;
            if self.slab.live() >= MAX_CONNS_PER_SHARD {
                close_fd(fd); // at the shard cap: refuse
                continue;
            }
            let peer_ip = peer_ip_from_storage(&ss);
            set_nonblocking(fd);
            set_nodelay(fd);
            set_nosigpipe(fd);
            // REACTOR-LEVEL per-source connection-limit gate — read the source's
            // active count BEFORE this connection's increment (proven admission rule
            // `Reactor.Stage.ConnLimit.admits`: cap 0 = unlimited, else active < cap).
            let now = Instant::now();
            let cap = crate::config::max_connections();
            let over_limit = cap != 0 && self.standing.active(peer_ip) >= cap;
            // EXACTLY ONE increment per conn entering the slab, matched by one
            // decrement at `close` (conn_conservation).
            self.standing.on_accept(peer_ip);
            // REACTOR-LEVEL per-source REQUEST-RATE gate — note this arrival against
            // the source's sliding window; over the `rate-limit` cap ⇒ the REAL `429`
            // (`rate_limit_fires`, `Reactor/StandingCounters.lean`). Precedence: the
            // connection `503` first, then the rate `429`.
            let over_rate = self.standing.rate_note(
                peer_ip,
                crate::config::rate_limit(),
                crate::config::rate_window(),
                now,
            );
            let conn = Conn {
                fd,
                peer_ip,
                conn_seq: 0,
                acc: self.gw.pool().take(),
                resp: None,
                sent: 0,
                req_keepalive: false,
                keepalive: false,
                h2c: false,
                serving: false,
                read_armed: false,
                write_armed: false,
                rd_streak: 0,
                rd_skip: 0,
                wr_streak: 0,
                wr_skip: 0,
                req_start: now,
                logrec: None,
                hdr_start: now,
                headers_done: false,
            };
            let slot = self.slab.insert(conn);
            if over_limit {
                // At/over the per-source cap: stage the REAL 503 and close after the
                // send WITHOUT dispatching to the serve (keepalive stays false). The
                // decrement at `close` matches the accept increment exactly.
                if let Some(conn) = self.slab.get(slot) {
                    let mut resp = self.gw.pool().take();
                    resp.extend_from_slice(CONN_LIMIT_503);
                    conn.resp = Some(resp);
                    conn.sent = 0;
                    conn.keepalive = false;
                }
                self.want_write(slot);
                continue;
            } else if over_rate {
                // Over the per-source request-rate window: stage the REAL 429 and close
                // after the send WITHOUT dispatching.
                if let Some(conn) = self.slab.get(slot) {
                    let mut resp = self.gw.pool().take();
                    resp.extend_from_slice(RATE_LIMIT_429);
                    conn.resp = Some(resp);
                    conn.sent = 0;
                    conn.keepalive = false;
                }
                self.want_write(slot);
                continue;
            }
            self.accepted += 1;
            if self.trace {
                // Evidence accepts are spreading across shards: each shard reports
                // its first won accept and periodic totals.
                if self.accepted == 1 || self.accepted % 64 == 0 {
                    eprintln!(
                        "dataplane: kqueue shard {} accepted connection #{}",
                        self.id, self.accepted
                    );
                }
            }
            // Inline fast path: try to read the request right now.
            self.want_read(slot);
        }
    }

    /// A response is waiting: drain the self-pipe, then every completed response
    /// from the mailbox, staging each and starting its send.
    fn on_wakeup(&mut self) {
        // Drain the self-pipe (coalesced wakeups may batch several bytes).
        let mut sink = [0u8; 64];
        loop {
            // SAFETY: reading into a local buffer from the non-blocking pipe read
            // end; a non-positive result (EAGAIN / EOF) ends the drain.
            let k =
                unsafe { libc::read(self.wake_rd, sink.as_mut_ptr() as *mut c_void, sink.len()) };
            if k <= 0 {
                break;
            }
        }
        // Collect finished responses first so the mailbox borrow is released
        // before the per-connection handlers run.
        let mut ready: Vec<KqDone> = Vec::new();
        while let Ok(done) = self.mrx.try_recv() {
            ready.push(done);
        }
        for mut done in ready {
            if let Some(conn) = self.slab.get(done.conn) {
                conn.serving = false;
                // REAL GZIP SEAM (`DRORB_RUST_GZIP=1`): replace the proven stored-block
                // gzip stage's (uncompressed) body with real flate2 DEFLATE. Keyed on the
                // response's own `Content-Encoding: gzip`; inert when unset / not gzipped.
                // Runs BEFORE keepalive detection so the rewritten Content-Length decides
                // self-delimitation. (Trusted, not verified.)
                if crate::gzip::enabled() {
                    crate::gzip::recompress(&mut done.resp);
                }
                conn.keepalive =
                    !conn.h2c && conn.req_keepalive && response_is_self_delimited(&done.resp);
                // State the connection disposition explicitly for strict HTTP/1.1
                // clients (never on raw h2c frames — they carry no HTTP/1.1 head).
                if !conn.h2c {
                    annotate_connection(&mut done.resp, conn.keepalive);
                }
                // OBSERVABILITY (mirrors `blocking::handle_conn`'s post-serve `emit`):
                // count this served response and write its access-log line, ONCE, at the
                // point the response is staged for send — the funnel every response
                // passes through. Skipped for raw h2c frames, exactly as blocking's h2c
                // path emits nothing. `backend = None`, as blocking's metered emit.
                if !conn.h2c {
                    crate::metrics::record(&done.resp, None);
                    if let Some((rl, client)) = &conn.logrec {
                        crate::access_log::log(*client, rl, &done.resp, None, conn.req_start);
                    }
                }
                conn.resp = Some(done.resp);
                conn.sent = 0;
                self.want_write(done.conn);
            }
            // else: connection already gone; drop the response (returns to pool).
        }
    }

    /// The connection is readable: an edge arrived, so drain it inline.
    fn on_readable(&mut self, slot: u32) {
        if let Some(conn) = self.slab.get(slot) {
            conn.rd_streak = 0;
            conn.rd_skip = 0;
        }
        self.recv_drain(slot, true);
    }

    /// The connection is writable: continue the pending send inline.
    fn on_writable(&mut self, slot: u32) {
        if let Some(conn) = self.slab.get(slot) {
            conn.wr_streak = 0;
            conn.wr_skip = 0;
        }
        self.send_drain(slot, true);
    }

    // --- inline fast paths -------------------------------------------------

    /// Submit-recv fast path: try the recv syscall immediately, subject to the
    /// adaptive backoff. On a WOULDBLOCK streak, skip the optimistic syscall and
    /// wait on `EVFILT_READ` instead.
    fn want_read(&mut self, slot: u32) {
        let skip = {
            let conn = match self.slab.get(slot) {
                Some(c) => c,
                None => return,
            };
            if conn.serving || conn.resp.is_some() {
                return; // not this connection's turn to read
            }
            if conn.rd_skip > 0 {
                conn.rd_skip -= 1;
                true
            } else {
                false
            }
        };
        if skip {
            self.arm_read(slot);
            return;
        }
        self.recv_drain(slot, false);
    }

    /// Drain the socket's receive buffer inline: recv into the accumulation
    /// buffer and frame requests until a request is handed off, the socket would
    /// block, or the connection ends. `from_event` distinguishes a real readiness
    /// edge (where a WOULDBLOCK does not feed the backoff) from an optimistic
    /// inline attempt (where it does).
    fn recv_drain(&mut self, slot: u32, from_event: bool) {
        loop {
            let (fd, len) = {
                let conn = match self.slab.get(slot) {
                    Some(c) => c,
                    None => return,
                };
                if conn.serving || conn.resp.is_some() {
                    return;
                }
                conn.acc.reserve(RECV_CHUNK);
                (conn.fd, conn.acc.len())
            };
            // SAFETY: `reserve(RECV_CHUNK)` guaranteed capacity for RECV_CHUNK
            // bytes past `len`; the pointer is valid for that many bytes and the
            // kernel initializes the ones it reports written.
            let ptr = {
                let conn = self.slab.get(slot).unwrap();
                unsafe { conn.acc.as_mut_ptr().add(len) }
            };
            let n = unsafe { libc::recv(fd, ptr as *mut c_void, RECV_CHUNK, libc::MSG_DONTWAIT) };
            if n > 0 {
                {
                    let conn = self.slab.get(slot).unwrap();
                    // SAFETY: the kernel wrote `n` bytes into the reserved tail of
                    // `acc`; extending the logical length to cover them is sound.
                    unsafe { conn.acc.set_len(len + n as usize) };
                    conn.rd_streak = 0;
                    conn.rd_skip = 0;
                }
                match self.dispatch(slot) {
                    Disp::Served | Disp::Closed => return,
                    Disp::NeedMore => continue, // try to read more of the request
                }
            } else if n == 0 {
                return self.close(slot); // EOF
            } else {
                let e = std::io::Error::last_os_error();
                match e.raw_os_error() {
                    Some(libc::EAGAIN) => {
                        if !from_event {
                            let conn = self.slab.get(slot).unwrap();
                            conn.rd_streak = (conn.rd_streak + 1).min(BACKOFF_MAX);
                            conn.rd_skip = 1u32 << conn.rd_streak;
                        }
                        self.arm_read(slot);
                        return;
                    }
                    Some(libc::EINTR) => continue,
                    _ => return self.close(slot),
                }
            }
        }
    }

    /// Submit-send fast path: try the send syscall immediately, subject to the
    /// adaptive backoff, else wait on `EVFILT_WRITE`.
    fn want_write(&mut self, slot: u32) {
        let skip = {
            let conn = match self.slab.get(slot) {
                Some(c) => c,
                None => return,
            };
            if conn.resp.is_none() {
                return;
            }
            if conn.wr_skip > 0 {
                conn.wr_skip -= 1;
                true
            } else {
                false
            }
        };
        if skip {
            self.arm_write(slot);
            return;
        }
        self.send_drain(slot, false);
    }

    /// Drain the pending response to the socket inline: send the unsent remainder
    /// until it is all out (then advance the connection), the socket would block
    /// (then wait on `EVFILT_WRITE`), or an error closes the connection.
    fn send_drain(&mut self, slot: u32, from_event: bool) {
        loop {
            let (fd, ptr, remaining) = {
                let conn = match self.slab.get(slot) {
                    Some(c) => c,
                    None => return,
                };
                let resp = match &conn.resp {
                    Some(r) => r,
                    None => return,
                };
                let remaining = resp.len() - conn.sent;
                if remaining == 0 {
                    // Nothing left (defensive); treat as completed below.
                    (conn.fd, std::ptr::null::<u8>(), 0usize)
                } else {
                    (conn.fd, resp[conn.sent..].as_ptr(), remaining)
                }
            };
            if remaining == 0 {
                return self.on_send_complete(slot);
            }
            // SAFETY: `ptr`/`remaining` describe the unsent tail of the pooled
            // response buffer, valid until the send completes and it is released.
            let n = unsafe { libc::send(fd, ptr as *const c_void, remaining, libc::MSG_DONTWAIT) };
            if n > 0 {
                let done = {
                    let conn = self.slab.get(slot).unwrap();
                    conn.sent += n as usize;
                    conn.wr_streak = 0;
                    conn.wr_skip = 0;
                    let total = conn.resp.as_ref().map(|r| r.len()).unwrap_or(0);
                    conn.sent >= total
                };
                if done {
                    return self.on_send_complete(slot);
                }
                continue; // short write: send the rest
            } else if n == 0 {
                // No progress; wait for writability.
                self.arm_write(slot);
                return;
            } else {
                let e = std::io::Error::last_os_error();
                match e.raw_os_error() {
                    Some(libc::EAGAIN) => {
                        if !from_event {
                            let conn = self.slab.get(slot).unwrap();
                            conn.wr_streak = (conn.wr_streak + 1).min(BACKOFF_MAX);
                            conn.wr_skip = 1u32 << conn.wr_streak;
                        }
                        self.arm_write(slot);
                        return;
                    }
                    Some(libc::EINTR) => continue,
                    _ => return self.close(slot),
                }
            }
        }
    }

    /// The whole response is written: release it (returns to the pool), stop the
    /// write filter, and either advance to the next request (keep-alive) or close.
    fn on_send_complete(&mut self, slot: u32) {
        let keepalive = {
            let conn = match self.slab.get(slot) {
                Some(c) => c,
                None => return,
            };
            conn.resp = None;
            conn.sent = 0;
            conn.keepalive
        };
        self.disarm_write(slot);
        if keepalive {
            // A pipelined request may already be buffered; else read the next one.
            match self.dispatch(slot) {
                Disp::Served | Disp::Closed => {}
                Disp::NeedMore => self.want_read(slot),
            }
        } else {
            self.close(slot);
        }
    }

    // --- framing / dispatch ------------------------------------------------

    /// Try to frame one complete request from `conn.acc` and hand it to the serve
    /// gateway. Mirrors the io_uring shard's dispatch: h2c preface fork, then
    /// HTTP/1.1 framing. Does not itself read — the caller drives the fast path.
    fn dispatch(&mut self, slot: u32) -> Disp {
        // SLOWLORIS gate — checked on each read-driven re-entry, BEFORE framing. If the
        // header phase (since accept) has overrun `slowloris-timeout` and the first
        // request has not yet been dispatched, drop with the REAL proven `408`
        // (`slowloris_fires`). Checking before framing refuses a slow DRIP that finally
        // completes its head past the deadline (the classic slowloris drop).
        let timeout = crate::config::slowloris_timeout();
        if !timeout.is_zero() {
            let expired = match self.slab.get(slot) {
                Some(c) => {
                    !c.headers_done
                        && crate::standing::header_expired(timeout, c.hdr_start, Instant::now())
                }
                None => return Disp::Closed,
            };
            if expired {
                if let Some(conn) = self.slab.get(slot) {
                    let mut resp = self.gw.pool().take();
                    resp.extend_from_slice(SLOWLORIS_408);
                    conn.resp = Some(resp);
                    conn.sent = 0;
                    conn.keepalive = false;
                }
                self.want_write(slot);
                return Disp::Served;
            }
        }
        // h2c preface still arriving: wait for the full 16-octet head.
        {
            let conn = match self.slab.get(slot) {
                Some(c) => c,
                None => return Disp::Closed,
            };
            if !conn.h2c && conn.acc.len() < H2_PREFACE.len() && H2_PREFACE.starts_with(&conn.acc) {
                return Disp::NeedMore;
            }
        }

        // h2c prior-knowledge: the connection leaves the reactor for good — the
        // interactive engine host threads ONE verified engine state across
        // socket reads on a dedicated thread (the same fork the blocking host
        // and the io_uring shard make at their preface peeks).
        let is_h2c = {
            let conn = self.slab.get(slot).unwrap();
            !conn.h2c && conn.acc.starts_with(H2_PREFACE)
        };
        if is_h2c {
            self.h2c_handoff(slot);
            return Disp::Closed;
        }

        let framed = {
            let conn = self.slab.get(slot).unwrap();
            match next_request(&conn.acc) {
                Frame::Complete(total) => {
                    // MIXED-PORT OPENER CLASSIFICATION — the same rule as the
                    // blocking host and the io_uring shard: a FIRST flight whose
                    // request line has no `HTTP/` version token is neither
                    // protocol's well-formed opener — not an HTTP/1.x request, and
                    // not the H2 preface (that forked to the engine at the peek
                    // above). Terminate without a reply, the one answer both
                    // protocols assign (RFC 9113 §3.4 invalid-preface connection
                    // error — an HTTP/1.1 status line is only frame garbage to an
                    // H2 client; RFC 9112 §2.2/§3 close on a malformed
                    // request-line).
                    if !conn.headers_done
                        && crate::http::opener_lacks_http_version(&conn.acc[..total])
                    {
                        self.close(slot);
                        return Disp::Closed;
                    }
                    let conn = self.slab.get(slot).unwrap();
                    let mut req = self.gw.pool().take();
                    req.extend_from_slice(&conn.acc[..total]);
                    conn.acc.drain(..total);
                    conn.req_keepalive = request_wants_keepalive(&req);
                    conn.serving = true;
                    conn.headers_done = true; // header phase complete
                    Some(req)
                }
                Frame::NeedMore => None,
                Frame::Oversize => {
                    self.close(slot);
                    return Disp::Closed;
                }
            }
        };
        match framed {
            Some(req) => self.submit_metered(slot, req),
            None => Disp::NeedMore,
        }
    }

    /// Fork an h2c prior-knowledge connection out of the reactor to the
    /// interactive engine host (`h2::host_conn`): ONE verified engine state
    /// threaded across socket reads on a dedicated thread. SETTINGS
    /// synchronization, PING liveness probes, and WINDOW_UPDATE-paced response
    /// bodies all arrive AFTER the client's first flight (RFC 9113
    /// §6.5.3/§6.7/§6.9), so a one-shot reactor crossing cannot answer them.
    ///
    /// Mirrors `close`'s bookkeeping except the fd itself, whose ownership
    /// moves to the host thread: the kqueue filters are deleted explicitly (the
    /// fd stays open, so closing cannot deregister them), the per-source
    /// standing counter decrements (the connection leaves this reactor's
    /// accounting at handoff, not at connection end), and the slab entry drops.
    fn h2c_handoff(&mut self, slot: u32) {
        let (fd, ip, read_armed, write_armed, burst) = {
            let conn = match self.slab.get(slot) {
                Some(c) => c,
                None => return,
            };
            let mut burst = Vec::with_capacity(conn.acc.len());
            burst.extend_from_slice(&conn.acc);
            (
                conn.fd,
                conn.peer_ip,
                conn.read_armed,
                conn.write_armed,
                burst,
            )
        };
        if read_armed {
            self.changes.push(kev(
                fd as usize,
                libc::EVFILT_READ,
                libc::EV_DELETE,
                slot as usize,
            ));
        }
        if write_armed {
            self.changes.push(kev(
                fd as usize,
                libc::EVFILT_WRITE,
                libc::EV_DELETE,
                slot as usize,
            ));
        }
        self.standing.on_close(ip);
        self.slab.remove(slot); // drops Conn: acc/resp buffers return to pool
        // SAFETY: the slab entry is gone and its filters are deleted, so the new
        // TcpStream is the fd's sole owner; it moves to the host thread and
        // closes there.
        let stream = unsafe { std::net::TcpStream::from_raw_fd(fd) };
        let _ = stream.set_nonblocking(false); // host reads block under its timeouts
        std::thread::spawn(move || crate::h2::host_conn(stream, &burst));
    }

    /// Hand a framed HTTP/1.1 request across the METERED serve seam — the same
    /// dispatch `blocking::handle_conn` and the io_uring shard run: the
    /// connection's client address (accept peer, or the forwarded client when the
    /// peer is a trusted proxy) and per-connection request index are in scope, so
    /// the proven IP-filter and rate gates fire. The default (no braid, no/empty
    /// config) is the config-driven metered fold over the empty config =
    /// `servePipelineOfMetered defaultDeployment`, byte-identical to the old plain
    /// `drorb_serve` where no gate fires (`servePipelineOfMetered_default`). Braid
    /// (`DRORB_BRAID=1`) folds over `braidedDeployment` (the proven forward-auth
    /// gate + request-id echo at the head). Delivered back to this reactor's
    /// mailbox + self-pipe.
    fn submit_metered(&mut self, slot: u32, req: PooledBuf) -> Disp {
        // The connection context the metered gates read: the client address and
        // the per-connection request index, which advances once per served request
        // so a burst on ONE kept-alive connection depletes the rate bucket.
        let (peer_ip, seq) = {
            let conn = match self.slab.get(slot) {
                Some(c) => c,
                None => return Disp::Closed,
            };
            let seq = conn.conn_seq;
            conn.conn_seq = conn.conn_seq.wrapping_add(1);
            (conn.peer_ip, seq)
        };
        let meter = Meter {
            client: crate::blocking::client_addr(&req, peer_ip),
            seq,
        };
        // OBSERVABILITY capture (mirrors `blocking::handle_conn` before the serve call):
        // the effective client + request line + start instant, threaded to the staging
        // point (`on_wakeup`) where the metric and access-log line are emitted. The
        // request line is parsed only when the log is enabled.
        if let Some(conn) = self.slab.get(slot) {
            conn.req_start = Instant::now();
            conn.logrec = if crate::access_log::enabled() {
                Some((crate::access_log::ReqLine::parse(&req), meter.client))
            } else {
                None
            };
        }
        let reply = ServeReply::Reactor(self.mtx.clone(), self.wake_wr, slot);
        // The SAME metered-fold choice `blocking::handle_conn` makes: the braided
        // deployment when braid-marked, else the config-driven metered fold (which
        // defaults to `defaultDeployment` for an empty/absent config). Both frame
        // `req` into their own pooled buffer, so the pooled `req` here drops back to
        // the pool at the end of this call.
        let ok = if crate::config::braid_enabled() {
            self.gw.submit_metered_braided_bytes(&req, meter, reply)
        } else {
            let cfg = crate::config::get();
            let cfg_bytes: &[u8] = cfg
                .as_ref()
                .map(|d| d.config_text.as_slice())
                .unwrap_or(&[]);
            self.gw
                .submit_metered_cfg_bytes(cfg_bytes, &req, meter, reply)
        };
        if ok {
            Disp::Served
        } else {
            self.close(slot);
            Disp::Closed
        }
    }

    // --- kqueue registration ----------------------------------------------

    fn arm_read(&mut self, slot: u32) {
        let (fd, need) = {
            let conn = match self.slab.get(slot) {
                Some(c) => c,
                None => return,
            };
            let need = !conn.read_armed;
            conn.read_armed = true;
            (conn.fd, need)
        };
        if need {
            self.changes.push(kev(
                fd as usize,
                libc::EVFILT_READ,
                libc::EV_ADD | libc::EV_CLEAR,
                slot as usize,
            ));
        }
    }

    fn arm_write(&mut self, slot: u32) {
        let (fd, need) = {
            let conn = match self.slab.get(slot) {
                Some(c) => c,
                None => return,
            };
            let need = !conn.write_armed;
            conn.write_armed = true;
            (conn.fd, need)
        };
        if need {
            self.changes.push(kev(
                fd as usize,
                libc::EVFILT_WRITE,
                libc::EV_ADD | libc::EV_CLEAR,
                slot as usize,
            ));
        }
    }

    fn disarm_write(&mut self, slot: u32) {
        let fd = {
            let conn = match self.slab.get(slot) {
                Some(c) => c,
                None => return,
            };
            if !conn.write_armed {
                return;
            }
            conn.write_armed = false;
            conn.fd
        };
        self.changes.push(kev(
            fd as usize,
            libc::EVFILT_WRITE,
            libc::EV_DELETE,
            slot as usize,
        ));
    }

    /// Close a connection: drop its slab entry (buffers return to the pool) and
    /// close the fd, which removes all its kqueue registrations automatically.
    fn close(&mut self, slot: u32) {
        if let Some(conn) = self.slab.get(slot) {
            let fd = conn.fd;
            let ip = conn.peer_ip;
            // Decrement the per-source standing counter EXACTLY ONCE — the single
            // close funnel every connection exits through, matching the accept
            // increment on every path (conn_conservation; no leak).
            self.standing.on_close(ip);
            self.slab.remove(slot); // drops Conn: acc/resp buffers return to pool
            close_fd(fd);
        }
    }
}

// --- fd / socket helpers --------------------------------------------------

/// Decode the accept peer sockaddr the kernel filled into a client `IpAddr` — the
/// metered IP-filter gate's default decision address. Unknown families fall back
/// to the unspecified IPv4 address (which the default-admit ruleset passes),
/// matching the io_uring shard's and blocking host's unresolvable-peer fallback.
fn peer_ip_from_storage(ss: &libc::sockaddr_storage) -> IpAddr {
    match ss.ss_family as c_int {
        libc::AF_INET => {
            // SAFETY: the family tag says this storage holds a `sockaddr_in`.
            let sin = unsafe { &*(ss as *const _ as *const libc::sockaddr_in) };
            // `s_addr` is network byte order; its in-memory bytes are the octets.
            IpAddr::V4(Ipv4Addr::from(sin.sin_addr.s_addr.to_ne_bytes()))
        }
        libc::AF_INET6 => {
            // SAFETY: the family tag says this storage holds a `sockaddr_in6`.
            let sin6 = unsafe { &*(ss as *const _ as *const libc::sockaddr_in6) };
            IpAddr::V6(Ipv6Addr::from(sin6.sin6_addr.s6_addr))
        }
        _ => IpAddr::V4(Ipv4Addr::UNSPECIFIED),
    }
}

fn empty_kevent() -> libc::kevent {
    libc::kevent {
        ident: 0,
        filter: 0,
        flags: 0,
        fflags: 0,
        data: 0,
        udata: std::ptr::null_mut(),
    }
}

fn kev(ident: usize, filter: i16, flags: u16, udata: usize) -> libc::kevent {
    libc::kevent {
        ident: ident as libc::uintptr_t,
        filter,
        flags,
        fflags: 0,
        data: 0,
        udata: udata as *mut c_void,
    }
}

fn close_fd(fd: RawFd) {
    // SAFETY: `fd` is a live descriptor this reactor owns; closing it once is
    // sound and removes it from any kqueue it was registered on.
    unsafe {
        libc::close(fd);
    }
}

fn set_nonblocking(fd: RawFd) {
    // SAFETY: F_GETFL/F_SETFL on a live fd; failures leave the fd usable (the
    // reactor still treats WOULDBLOCK correctly).
    unsafe {
        let fl = libc::fcntl(fd, libc::F_GETFL, 0);
        if fl >= 0 {
            libc::fcntl(fd, libc::F_SETFL, fl | libc::O_NONBLOCK);
        }
    }
}

fn set_nodelay(fd: RawFd) {
    let on: c_int = 1;
    // SAFETY: setting TCP_NODELAY on a connected TCP socket; a failure is
    // non-fatal (only affects latency, not correctness).
    unsafe {
        libc::setsockopt(
            fd,
            libc::IPPROTO_TCP,
            libc::TCP_NODELAY,
            &on as *const c_int as *const c_void,
            std::mem::size_of::<c_int>() as socklen_t,
        );
    }
}

fn set_nosigpipe(fd: RawFd) {
    let on: c_int = 1;
    // SAFETY: SO_NOSIGPIPE makes a broken-pipe write fail with EPIPE instead of
    // raising SIGPIPE; a failure is non-fatal (the global SIG_IGN still guards).
    unsafe {
        libc::setsockopt(
            fd,
            libc::SOL_SOCKET,
            libc::SO_NOSIGPIPE,
            &on as *const c_int as *const c_void,
            std::mem::size_of::<c_int>() as socklen_t,
        );
    }
}

/// Bind a fresh listening socket on `addr` with `SO_REUSEPORT` (+ `SO_REUSEADDR`),
/// so the kernel load-balances accepts across every shard that binds the same
/// address. Returns the non-blocking listener fd.
fn bind_reuseport(addr: SocketAddr) -> std::io::Result<RawFd> {
    let domain = if addr.is_ipv4() {
        libc::AF_INET
    } else {
        libc::AF_INET6
    };
    // SAFETY: each libc call is checked; sockaddr storage is a correctly-sized,
    // zero-initialized struct for the address family, and the fd is closed on any
    // subsequent failure.
    unsafe {
        let fd = libc::socket(domain, libc::SOCK_STREAM, 0);
        if fd < 0 {
            return Err(std::io::Error::last_os_error());
        }
        let on: c_int = 1;
        let set = |opt: c_int| {
            libc::setsockopt(
                fd,
                libc::SOL_SOCKET,
                opt,
                &on as *const c_int as *const c_void,
                std::mem::size_of::<c_int>() as socklen_t,
            );
        };
        set(libc::SO_REUSEADDR);
        set(libc::SO_REUSEPORT);
        set(libc::SO_NOSIGPIPE);

        let rc = match addr {
            SocketAddr::V4(a) => {
                let mut s: libc::sockaddr_in = std::mem::zeroed();
                s.sin_len = std::mem::size_of::<libc::sockaddr_in>() as u8;
                s.sin_family = libc::AF_INET as sa_family_t;
                s.sin_port = a.port().to_be();
                s.sin_addr = libc::in_addr {
                    s_addr: u32::from_ne_bytes(a.ip().octets()),
                };
                libc::bind(
                    fd,
                    &s as *const libc::sockaddr_in as *const libc::sockaddr,
                    std::mem::size_of::<libc::sockaddr_in>() as socklen_t,
                )
            }
            SocketAddr::V6(a) => {
                let mut s: libc::sockaddr_in6 = std::mem::zeroed();
                s.sin6_len = std::mem::size_of::<libc::sockaddr_in6>() as u8;
                s.sin6_family = libc::AF_INET6 as sa_family_t;
                s.sin6_port = a.port().to_be();
                s.sin6_addr = libc::in6_addr {
                    s6_addr: a.ip().octets(),
                };
                libc::bind(
                    fd,
                    &s as *const libc::sockaddr_in6 as *const libc::sockaddr,
                    std::mem::size_of::<libc::sockaddr_in6>() as socklen_t,
                )
            }
        };
        if rc < 0 {
            let e = std::io::Error::last_os_error();
            libc::close(fd);
            return Err(e);
        }
        if libc::listen(fd, 1024) < 0 {
            let e = std::io::Error::last_os_error();
            libc::close(fd);
            return Err(e);
        }
        set_nonblocking(fd);
        Ok(fd)
    }
}
