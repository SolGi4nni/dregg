//! A fixed-capacity pool of reusable byte buffers.
//!
//! The hot path — receive request bytes, hand them to the proven core, write
//! the response bytes back — needs three transient buffers per request: the
//! connection's accumulation buffer, the request buffer handed across the serve
//! seam, and the response buffer handed back. Allocating and freeing these per
//! request is the steady-state allocation the high-performance IO path is meant
//! to remove.
//!
//! [`BufferPool`] holds a free list of `Vec<u8>` that are checked out as
//! [`PooledBuf`] and returned to the list when the `PooledBuf` is dropped —
//! from whichever thread drops it, so a buffer can travel from a connection
//! worker to the serve thread and back and still recycle to the same pool. In
//! steady state (free list warm) a checkout is a `Vec::pop` and a return is a
//! `clear` + `push`: no allocation, no `free`. The list grows only when demand
//! exceeds the warm set, and is capped so a burst cannot retain buffers without
//! bound.
//!
//! ## Allocation profile
//!
//! Once the free list has served its first `N` concurrent buffers, the Rust
//! host performs **zero heap allocation per request** for these buffers. The
//! remaining per-request allocations live *inside the Lean runtime*: the seam
//! `drorb_serve : ByteArray -> ByteArray` consumes an owned input `ByteArray`
//! and returns an owned output `ByteArray`, so the runtime allocates one of each
//! per call on its GC heap. That copy-once discipline is intrinsic to the proven
//! ABI (the core is a pure `ByteArray -> ByteArray` function); the host cannot
//! remove it without changing that ABI. The host-side buffers this pool governs
//! are the ones the host *can* keep allocation-free, and does.

use std::collections::HashMap;
use std::net::{SocketAddr, TcpStream};
use std::ops::{Deref, DerefMut};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

/// A pool of reusable byte buffers shared across the host's threads.
pub struct BufferPool {
    free: Mutex<Vec<Vec<u8>>>,
    /// Capacity a freshly minted buffer reserves, so early requests do not pay
    /// repeated `realloc` as they fill.
    buf_cap: usize,
    /// Ceiling on retained free buffers. A returned buffer beyond this is
    /// dropped rather than retained, bounding idle memory after a burst.
    max_retained: usize,
}

impl BufferPool {
    /// A pool that mints buffers with `buf_cap` reserved capacity and retains at
    /// most `max_retained` idle buffers on the free list.
    pub fn new(buf_cap: usize, max_retained: usize) -> Arc<Self> {
        Arc::new(BufferPool {
            free: Mutex::new(Vec::new()),
            buf_cap,
            max_retained,
        })
    }

    /// Check out a cleared buffer. Reuses a free-list entry when one is warm,
    /// else mints a fresh buffer with the pool's reserve capacity.
    pub fn take(self: &Arc<Self>) -> PooledBuf {
        let buf = {
            let mut free = self.free.lock().unwrap();
            free.pop()
        }
        .unwrap_or_else(|| Vec::with_capacity(self.buf_cap));
        PooledBuf {
            buf,
            pool: Arc::clone(self),
        }
    }

    /// Return a buffer to the free list, or drop it if the list is at its cap.
    fn give_back(&self, mut buf: Vec<u8>) {
        buf.clear();
        let mut free = self.free.lock().unwrap();
        if free.len() < self.max_retained {
            free.push(buf);
        }
        // else: drop `buf`, releasing its allocation — the burst is over.
    }
}

/// A byte buffer on loan from a [`BufferPool`]. Derefs to its `Vec<u8>`; returns
/// itself to the pool (cleared) on drop, regardless of which thread drops it.
pub struct PooledBuf {
    buf: Vec<u8>,
    pool: Arc<BufferPool>,
}

impl Deref for PooledBuf {
    type Target = Vec<u8>;
    fn deref(&self) -> &Vec<u8> {
        &self.buf
    }
}

impl DerefMut for PooledBuf {
    fn deref_mut(&mut self) -> &mut Vec<u8> {
        &mut self.buf
    }
}

impl Drop for PooledBuf {
    fn drop(&mut self) {
        // Move the inner buffer out (leaving an empty, allocation-free Vec) and
        // hand it back to the pool for reuse.
        let buf = std::mem::take(&mut self.buf);
        self.pool.give_back(buf);
    }
}

/// An idle upstream socket parked in a [`ConnPool`], with the wall-clock instant
/// it was returned so a socket idle past the pool's max age is discarded rather
/// than reused (an upstream commonly closes a long-idle keep-alive connection, and
/// a socket sitting past the max age is likely half-closed).
struct IdleConn {
    stream: TcpStream,
    returned: Instant,
}

/// A per-backend cache of idle keep-alive upstream sockets, keyed by the backend's
/// socket address and shared across the host's connection threads.
///
/// Before this, every reverse-proxy forward opened a FRESH TCP connection to the
/// chosen backend (a `connect(2)` + three-way handshake per request) and dropped
/// the socket after the reply. This pool keeps a bounded set of already-connected,
/// message-boundary-clean sockets per backend: a forward first tries to
/// [`checkout`](ConnPool::checkout) an idle socket for its backend and reuses it,
/// falling back to a fresh dial only when none is warm (or the warm one proved
/// stale). After a CLEAN, fully-framed keep-alive reply the socket is
/// [`checkin`](ConnPool::checkin)ed for the next forward.
///
/// ## Reuse safety
///
/// A socket is only ever checked in when the whole upstream reply was consumed to
/// its framed end (a known `Content-Length`, fully delivered) AND the upstream did
/// not signal `Connection: close` — i.e. the socket sits exactly at the next
/// request boundary with an empty receive buffer and an upstream willing to serve
/// another request on it. On checkout the socket is additionally probed live (a
/// non-blocking peek): a peer FIN, unexpected pending bytes, or any error retires
/// it, so a socket the upstream closed while idle is never reused. A reuse that
/// still races a close surfaces as a write/read error on the forward, where the
/// caller retries once with a fresh dial — nothing has reached the client yet.
pub struct ConnPool {
    idle: Mutex<HashMap<SocketAddr, Vec<IdleConn>>>,
    /// Ceiling on idle sockets retained per backend address; a check-in beyond it
    /// drops the socket (closing it), bounding idle fds after a burst.
    max_idle_per_host: usize,
    /// A socket idle longer than this on checkout is retired unconditionally.
    max_idle_age: Duration,
    /// Count of forwards that REUSED a pooled socket (skipped the dial). Read for
    /// operator introspection / the reuse-observability check.
    reused: AtomicU64,
    /// Count of forwards that opened a FRESH connection (pool miss or stale entry).
    dialed: AtomicU64,
}

impl ConnPool {
    /// A pool retaining at most `max_idle_per_host` idle sockets per backend and
    /// retiring any socket idle longer than `max_idle_age` on checkout.
    pub fn new(max_idle_per_host: usize, max_idle_age: Duration) -> Arc<Self> {
        Arc::new(ConnPool {
            idle: Mutex::new(HashMap::new()),
            max_idle_per_host,
            max_idle_age,
            reused: AtomicU64::new(0),
            dialed: AtomicU64::new(0),
        })
    }

    /// Take a live idle socket for `addr`, or `None` when none is warm. Entries are
    /// popped most-recently-returned first (warmest); each candidate past the max
    /// idle age or failing the liveness probe is discarded (closed) and the next is
    /// tried. A returned socket carries no read/write timeout — the caller sets the
    /// forward's timeouts on it exactly as on a fresh dial.
    pub fn checkout(&self, addr: SocketAddr) -> Option<TcpStream> {
        let now = Instant::now();
        let mut idle = self.idle.lock().unwrap();
        let list = idle.get_mut(&addr)?;
        while let Some(c) = list.pop() {
            if now.duration_since(c.returned) > self.max_idle_age {
                continue; // too old: drop (its socket closes on `c`'s drop)
            }
            if Self::is_reusable(&c.stream) {
                return Some(c.stream);
            }
            // else: half-closed / dirty — drop and try the next.
        }
        None
    }

    /// Park `stream` as an idle socket for `addr`, ready for the next forward. The
    /// caller's contract: only check in a socket sitting exactly at a request
    /// boundary (the whole framed reply consumed) whose upstream did not signal
    /// `Connection: close`. A socket beyond the per-host cap is dropped (closed)
    /// rather than retained.
    pub fn checkin(&self, addr: SocketAddr, stream: TcpStream) {
        // A parked socket must not carry the forward's read/write deadlines into
        // its idle life, and reuse re-derives them, so clear them here.
        stream.set_read_timeout(None).ok();
        stream.set_write_timeout(None).ok();
        let mut idle = self.idle.lock().unwrap();
        let list = idle.entry(addr).or_default();
        if list.len() < self.max_idle_per_host {
            list.push(IdleConn {
                stream,
                returned: Instant::now(),
            });
        }
        // else: drop `stream`, closing it — the idle set for this backend is full.
    }

    /// Record that a forward reused a pooled socket (skipped a dial).
    pub fn note_reused(&self) {
        self.reused.fetch_add(1, Ordering::Relaxed);
    }

    /// Record that a forward opened a fresh connection (pool miss / stale entry).
    pub fn note_dialed(&self) {
        self.dialed.fetch_add(1, Ordering::Relaxed);
    }

    /// `(reused, dialed)` forward counts since start — for the reuse-observability
    /// check and operator introspection.
    pub fn stats(&self) -> (u64, u64) {
        (
            self.reused.load(Ordering::Relaxed),
            self.dialed.load(Ordering::Relaxed),
        )
    }

    /// Whether an idle socket is still reusable: a non-blocking `MSG_PEEK` that
    /// distinguishes "open, nothing pending" (reusable) from "peer FIN" (`Ok(0)`),
    /// "unexpected pending bytes" (an out-of-contract upstream — unsafe to reuse),
    /// or any socket error. The blocking mode is restored before return so the
    /// socket behaves exactly as a fresh dial for the forward.
    fn is_reusable(stream: &TcpStream) -> bool {
        if stream.set_nonblocking(true).is_err() {
            return false;
        }
        let mut probe = [0u8; 1];
        let ok = match stream.peek(&mut probe) {
            // Peer sent FIN (clean close) — the socket is dead.
            Ok(0) => false,
            // Bytes already pending before we sent a request: the upstream is out
            // of contract (or these are stale) — retire it rather than corrupt the
            // next reply.
            Ok(_) => false,
            // No data buffered and the peer has not closed: open and clean.
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => true,
            Err(_) => false,
        };
        // Restore blocking so the caller's timed reads/writes behave as on a dial.
        if stream.set_nonblocking(false).is_err() {
            return false;
        }
        ok
    }
}
