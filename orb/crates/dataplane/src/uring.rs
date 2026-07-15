//! The high-performance Linux IO path: an io_uring accept/recv/send event loop.
//!
//! This is the preferred IO path on Linux. It replaces the thread-per-connection
//! blocking model with a small number of **shards** — one event-loop thread per
//! core — each driving its own `io_uring` instance over its own connection set.
//! Accept, receive and send are submitted as SQEs and reaped as CQEs in batches;
//! a shard thread never blocks on a single connection, so one thread services
//! thousands of connections. This is the share-nothing reactor model: no
//! connection state, buffer, or slab is shared between shards.
//!
//! ## The one shared resource, and where the ceiling is
//!
//! The proven core is a pure `ByteArray -> ByteArray` transform, so shards need
//! no shared mutable engine state to run it — but the Lean runtime is a
//! process-global singleton, so there is exactly one runtime-owner thread (see
//! `serve`). Every shard hands its completed requests to that one thread over
//! the gateway channel and is woken with the response through its own eventfd.
//! The IO fabric (accept/recv/send, framing) scales across all shard cores; the
//! serve transform does not. The steady-state throughput ceiling is therefore
//! `1 / (serve latency)` regardless of shard count: the single runtime owner is
//! the bottleneck, and adding shards past the point that keeps the owner busy
//! only adds scheduling contention, not throughput.
//!
//! ## Copy discipline — two modes
//!
//! The **default** loop uses ordinary pooled receive buffers and a copied response:
//! recv into an accumulation `Vec`, copy the framed request into an owned buffer
//! (copy #1), and after the serve crossing copy the proven response bytes into a
//! pooled send buffer (copy #5).
//!
//! The **zero-copy mode** (`zc`, opt-in via `DRORB_ZC=1`) removes both
//! shell-owned full-payload copies, realizing in the running bytes what the
//! `Datapath` and `Uring` Lean theories prove:
//!
//! * **Receive** goes through a provided-buffer ring ([`crate::bufring`]). The
//!   kernel places the datagram into a ring slot and *lends* the slot to the
//!   completion. When a whole request arrives in one slot with nothing pipelined
//!   behind it, the shard hands the serve thread a **borrowed view** of the slot
//!   (`serve::BorrowedReq`) — no owned request copy (copy #1 removed) — and holds
//!   the buffer id *leased* across the serve. The id is *recycled exactly once*,
//!   when the response returns. This is the running counterpart of the proven
//!   `Uring` model: the kernel's `deliver`, the shard's `held` lease, and the
//!   `recycle` back into the ring are the model's edges, and the "each lent id is
//!   recycled at most once per lease" discipline is exactly
//!   `Uring.recycle_at_most_once` (`Uring/RecycleOnce.lean`). The borrowed view is
//!   the running form of `Datapath/Span.lean`'s `SpanBytes` (a request named by an
//!   `(off, len)` window, not copied to be named). Requests that span slots or
//!   arrive pipelined fall back to the accumulation buffer (copy #1 retained for
//!   those) and recycle their slot immediately.
//!
//! * **Send** uses `IORING_OP_SEND_ZC` straight from the proven response's pooled
//!   bytes (copy #5 removed — no userspace copy into the kernel's send path). The
//!   response buffer is held until the kernel posts the zero-copy notification
//!   (`F_NOTIF`) that the send buffer is free, then released. This realizes the
//!   in-place write `Datapath/Serve.lean` proves (`writeInPlace` /
//!   `writeInPlace_faithful`): the finalized response bytes are put on the wire
//!   from the buffer they were built in, without an intervening copy.
//!
//! Copies #2–#4 (the owned-`ByteArray` FFI marshalling and the internal
//! `List UInt8` representation) are *above* the FFI and cannot be removed from the
//! shell; only #1 and #5 are shell-owned. Zero-copy mode keeps the serve output
//! byte-identical — it removes copies, never a byte.

use std::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr};
use std::os::fd::{FromRawFd, RawFd};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc::{Receiver, Sender, channel};
use std::time::{Duration, Instant};

use io_uring::{IoUring, cqueue, opcode, squeue, types};

use crate::bufring::BufRing;
use crate::cache::CacheProbe;
use crate::http::{
    Frame, H2_PREFACE, next_request, request_wants_keepalive, response_is_self_delimited,
};
use crate::pool::PooledBuf;
use crate::serve::{BorrowedReq, Meter, Seam, ServeGateway, ServeReply, ShardDone};

/// Bytes offered to the kernel per receive (and per provided-buffer slot).
const RECV_CHUNK: usize = 16384;
/// SQ/CQ depth per shard.
const RING_ENTRIES: u32 = 4096;
/// Cap on live connections per shard; new accepts beyond it are closed.
const MAX_CONNS_PER_SHARD: usize = 16384;
/// While any NATIVE proxy dial is in flight, wake the shard at least this often to
/// sweep for upstream ops that have blown their per-op deadline (see
/// [`proxy_timeout`] / [`sweep_proxy_timeouts`]). Bounds how late past the deadline
/// a hung-upstream 502 can arrive; irrelevant to the hot path (only armed when a
/// dial is outstanding). 50 ms.
const PROXY_SWEEP_NS: u32 = 50_000_000;
/// Provided-buffer ring: group id and entry count (power of two). Each entry is
/// `RECV_CHUNK` bytes, so the ring costs `BR_ENTRIES * RECV_CHUNK` per shard.
const BR_BGID: u16 = 1;
const BR_ENTRIES: u16 = 1024;

/// Zero-copy datapath counters, so a run can *prove* the running path actually
/// took the buf_ring borrow + SendZc route rather than silently falling back.
/// Summarized by [`stats`] at shutdown.
pub static ZC_BORROW: AtomicU64 = AtomicU64::new(0);
pub static ZC_FALLBACK: AtomicU64 = AtomicU64::new(0);
pub static ZC_NOTIF: AtomicU64 = AtomicU64::new(0);
pub static ZC_RECYCLE: AtomicU64 = AtomicU64::new(0);

/// Connections refused with a `503` by the reactor-level per-source connection cap
/// (`max-connections`). Live evidence that the DoS-protection gate actually fired.
pub static REFUSED_503: AtomicU64 = AtomicU64::new(0);

/// Connections refused with a `429` by the reactor-level per-source REQUEST-RATE cap
/// (`rate-limit`). Live evidence that the rate gate actually fired.
pub static REFUSED_429: AtomicU64 = AtomicU64::new(0);

/// Connections dropped with a `408` by the reactor-level SLOWLORIS header-timeout
/// (`slowloris-timeout`). Live evidence that the slow-header gate actually fired.
pub static TIMEDOUT_408: AtomicU64 = AtomicU64::new(0);

/// The canned `503 Service Unavailable` a source at/over its `max-connections` cap
/// receives at accept — the wire form of the proven `Reactor.Stage.ConnLimit.resp503`
/// (status `503`, body `busyBody`). `stage_response` inserts `Connection: close`
/// (no Connection header here) so the refused connection is torn down after the send.
const CONN_LIMIT_503: &[u8] =
    b"HTTP/1.1 503 Service Unavailable\r\nContent-Type: text/plain\r\nContent-Length: 36\r\n\r\nper-source connection limit reached\n";

/// The canned `429 Too Many Requests` a source over its `rate-limit` window receives
/// at accept — the wire form of the proven `Reactor.Stage.StickTable.resp429` /
/// `Reactor.Stage.Rate.resp429` (status `429`). `stage_response` inserts
/// `Connection: close` so the refused connection is torn down after the send.
const RATE_LIMIT_429: &[u8] =
    b"HTTP/1.1 429 Too Many Requests\r\nContent-Type: text/plain\r\nContent-Length: 20\r\n\r\nrate limit exceeded\n";

/// The canned `408 Request Timeout` a connection whose header phase overran
/// `slowloris-timeout` receives — the wire form of the proven
/// `Reactor.Stage.Slowloris.resp408` (status `408`). `stage_response` inserts
/// `Connection: close` so the dropped connection is torn down after the send.
const SLOWLORIS_408: &[u8] =
    b"HTTP/1.1 408 Request Timeout\r\nContent-Type: text/plain\r\nContent-Length: 23\r\n\r\nrequest header timeout\n";

/// A one-line summary of the zero-copy counters, or `None` if the zero-copy path
/// never ran. `borrow == recycle` is the running recycle-exactly-once check
/// (`Uring.recycle_at_most_once`): every lent-and-borrowed slot recycled once.
pub fn stats() -> Option<String> {
    let b = ZC_BORROW.load(Ordering::Relaxed);
    let f = ZC_FALLBACK.load(Ordering::Relaxed);
    let n = ZC_NOTIF.load(Ordering::Relaxed);
    let r = ZC_RECYCLE.load(Ordering::Relaxed);
    if b == 0 && f == 0 && n == 0 && r == 0 {
        None
    } else {
        Some(format!(
            "zero-copy datapath: buf_ring borrow-recv={b} (copy #1 removed), \
             fallback-recv={f} (copy #1 retained), SendZc notifications={n} \
             (copy #5 removed), buf_ring recycles={r} (recycle-once: borrow==recycle is {})",
            b == r
        ))
    }
}

// user_data tag space: high 32 bits classify the op, low 32 carry the slot.
const TAG_ACCEPT: u64 = 1 << 32;
const TAG_EVENTFD: u64 = 2 << 32;
const TAG_RECV: u64 = 3 << 32;
const TAG_SEND: u64 = 4 << 32;
const TAG_CLOSE: u64 = 5 << 32;
/// A provided-buffer-ring (buffer-select) receive; its completion carries a
/// buffer id in the CQE flags.
const TAG_RECV_BR: u64 = 6 << 32;
/// NATIVE upstream-proxy SQEs on a shard-owned SECOND socket (the `TAG_YIELD_PROXY`
/// effect realized without leaving the shard): `connect(2)` the proven-picked
/// backend, `send(2)` the forward request, then a `recv(2)` loop accumulating the
/// upstream reply. Their completions carry the same connection slot in the low
/// bits and drive the proxy dial state machine (`on_proxy_*`).
const TAG_PROXY_CONNECT: u64 = 7 << 32;
const TAG_PROXY_SEND: u64 = 8 << 32;
const TAG_PROXY_RECV: u64 = 9 << 32;
const TAG_MASK: u64 = 0xffff_ffff << 32;
const SLOT_MASK: u64 = 0xffff_ffff;

/// Signal a shard that a serve response is waiting in its mailbox, by writing to
/// its eventfd. Called from the serve thread.
pub fn wake(efd: RawFd) {
    let one: u64 = 1;
    // SAFETY: an 8-byte write to an eventfd is the documented wakeup; `efd` is a
    // live eventfd owned by the target shard for the process lifetime, and
    // `&one` is a valid 8-byte source. The write cannot block (the counter only
    // saturates near u64::MAX, far beyond in-flight wakeups).
    unsafe {
        libc::write(efd, &one as *const u64 as *const libc::c_void, 8);
    }
}

/// Per-connection state owned by a single shard. No field is shared across
/// shards; a `Conn` and its buffers live and die on one shard thread.
struct Conn {
    fd: RawFd,
    /// The accept peer's IP — the default client address the metered IP-filter gate
    /// decides on (overridden by a forwarded client when the peer is a trusted
    /// proxy; see `blocking::client_addr`). Captured from the accept sockaddr.
    peer_ip: IpAddr,
    /// Per-connection request index, threaded as the rate bucket's standing
    /// depletion: request 0 sees a full bucket, later requests on the same
    /// kept-alive connection find it draining. Advances once per served request —
    /// the io_uring analogue of `blocking::handle_conn`'s `conn_seq`.
    conn_seq: u64,
    /// Accumulation buffer: recv completions extend it; framing consumes it.
    /// Unused on the buf_ring borrow fast path; still holds partial/pipelined
    /// bytes on the fallback path.
    acc: PooledBuf,
    /// A leased provided-buffer id held across the serve crossing (zero-copy
    /// receive). Recycled exactly once, when the response returns or the
    /// connection closes.
    leased_bid: Option<u16>,
    /// Response being written, and how many of its bytes are already out.
    resp: Option<PooledBuf>,
    sent: usize,
    /// Zero-copy send bookkeeping for the current response. A `SendZc` posts a
    /// data completion and — when it set `F_MORE` — a later `F_NOTIF` marking its
    /// send buffer free. The response buffer is released only when every issued
    /// op's data completion is in AND every expected notification has arrived, so
    /// nothing is freed (or the slot reused) while the kernel still references it.
    zc_issued: u32,
    zc_data: u32,
    zc_notif_exp: u32,
    zc_notif: u32,
    zc_error: bool,
    /// The in-flight request's keep-alive intent (HTTP/1.1 framing).
    req_keepalive: bool,
    /// Whether this connection stays open after the in-flight response — the
    /// request's intent AND the response being self-delimited.
    keepalive: bool,
    /// h2c connections are served once then closed (no HTTP/1.1 keep-alive).
    h2c: bool,
    /// PHASE 0 effect seam: when `Some`, this connection has an effect-seam STEP or
    /// RESUME in flight, so the NEXT mailbox reply for this slot is an encoded
    /// `Step` (not a final response) and `on_wakeup` routes it to `on_step_reply`
    /// to decode + drive the next resume. `None` on the default metered path (the
    /// reply is a final response, staged and sent directly).
    step: Option<Box<StepState>>,
    /// NATIVE proxy dial in flight: when `Some`, this connection's parked serve
    /// (`step`) yielded `proxyDial`, and the shard is driving a SECOND socket to
    /// the proven-picked upstream via SQEs (connect → send → recv-loop) instead of
    /// deferring to a blocking thread. Carries the upstream fd, the forward request,
    /// and the growing upstream-reply accumulator. Cleared when the reply is
    /// complete (the bytes are threaded into `submit_resume`) or the dial fails.
    proxy: Option<Box<ProxyDial>>,
    /// The next mailbox reply for this slot is the CL-trust STREAMING HEAD
    /// (`drorb_serve_proxy_stream_head`), not a `Step`: `on_wakeup` routes it to
    /// `on_stream_head_reply` (send the head + start passthrough streaming, or fall back
    /// to the buffered resume on an empty — gzip — reply).
    awaiting_stream_head: bool,
    /// OBSERVABILITY: the per-request start instant, captured at dispatch (mirrors
    /// `blocking::handle_conn`'s `req_start`) and read at the response-sent point for
    /// the access-log duration. Reset on each request of a kept-alive connection.
    req_start: Instant,
    /// OBSERVABILITY: the request line + effective client captured at dispatch, but
    /// only when the access log is enabled (`None` when off — nothing is parsed and
    /// the log is skipped). Consumed at the response-sent point.
    logrec: Option<(crate::access_log::ReqLine, IpAddr)>,
    /// OBSERVABILITY: for the NATIVE passthrough-streaming proxy path, the transformed
    /// response head, retained so the whole streamed response can be recorded ONCE at
    /// `proxy_stream_finish` (status from the head, bytes = head + streamed body).
    stream_head: Option<Vec<u8>>,
    /// SLOWLORIS: when this connection's header phase began (captured at accept). The
    /// reactor drops the connection with a `408` if its FIRST request head has not
    /// completed within `slowloris-timeout` of this instant (the proven
    /// `Reactor.Stage.Slowloris.expired` decision on `hdr_start`).
    hdr_start: Instant,
    /// SLOWLORIS: set true once this connection's first request has been framed and
    /// dispatched — its header phase is over, so the slow-header gate no longer
    /// applies (classic first-header slowloris defense).
    headers_done: bool,
    /// ZERO-COPY BODY (`DRORB_SPAN=15`): the length of the request borrowed into the
    /// held lease (`leased_bid`), i.e. the echo body the split write splices straight
    /// from the buf_ring slot. Set at dispatch on the zero-copy borrow path; read at
    /// the split-response staging point. `0` when the request was not borrowed (the
    /// split path is unavailable then).
    req_len: usize,
    /// ZERO-COPY BODY (`DRORB_SPAN=15`): the in-flight split send — the Lean-computed
    /// response HEAD plus the borrowed body slot, written to the socket as ONE `writev`
    /// gather (head iovec + body iovec). `Some` only on the split path; the body is
    /// NEVER copied into a buffer (it is sliced from the held lease at send time).
    split: Option<Box<SplitSend>>,
}

/// Where a split send's body bytes live — a source referenced at send time and
/// gathered by `writev`, NEVER copied into an output buffer.
enum SplitBody {
    /// ZERO-COPY BODY (`DRORB_SPAN=15`): the borrowed request in the held buf_ring
    /// lease — `br.slice(bid, body_len)` (the echo body).
    Lease(u16),
    /// ZERO-COPY STATIC BODY (`DRORB_SPAN=23`): the process-static constant body
    /// (`crate::serve::static_bulk_body`) — a process-lifetime buffer, trivially
    /// valid for any in-flight send.
    Static(&'static [u8]),
}

/// The state of one in-flight ZERO-COPY-BODY split send (`DRORB_SPAN=15`/`=23`): the
/// small Lean-computed response HEAD and the referenced body (a held buf_ring slot, or
/// the process-static constant body), written to the socket as a single `writev`
/// gather so the body goes from its source buffer straight to the wire — never
/// appended into an output `ByteArray`.
struct SplitSend {
    /// The response HEAD the serve thread computed (`drorb_serve_split_head` /
    /// `drorb_serve_conformant_zc`): status line + headers + `Content-Length` + the
    /// blank-line separator, with the host's `Connection:` annotation. Small (no
    /// body). Kept alive for the in-flight writev.
    head: PooledBuf,
    /// The body source: sliced/referenced at send time and gathered by `writev`,
    /// NEVER copied into a buffer.
    body: SplitBody,
    body_len: usize,
    /// Total response bytes (head + body) acknowledged so far, across re-armed writevs
    /// on a short write.
    sent: usize,
    /// The gather array kept alive for the in-flight `writev` SQE (up to two iovecs:
    /// the unsent head remainder then the body, or just the body once the head is out).
    iov: [libc::iovec; 2],
    iov_n: u32,
}

/// The framing that delimits the upstream reply, decided once its head is seen.
#[derive(Clone, Copy)]
enum ReplyFraming {
    /// Head not yet complete (no CRLFCRLF seen).
    Unknown,
    /// `Content-Length`: the reply is complete at this absolute accumulator length
    /// (`head_end + content_length`).
    Fixed(usize),
    /// `Transfer-Encoding: chunked`: complete when the incremental parser sees the
    /// terminating zero-chunk.
    Chunked,
    /// Neither Content-Length nor chunked: close-delimited, complete only on EOF.
    Eof,
}

/// The in-flight NATIVE upstream-proxy dial state for one connection — the async,
/// SQE-driven analogue of `proxy_dial::forward` (connect → write request → read
/// reply), run on a SECOND shard-owned socket so the shard never blocks. Realizes
/// the `TAG_YIELD_PROXY` arm of the proven effect program: the upstream reply is
/// accumulated (required by the response-transform's gzip re-encode, the honest
/// residual `Reactor.DriveProxy` names) and threaded into `drorb_serve_resume`,
/// which computes `proxyRespTransform input upstream` — the SAME bytes the blocking
/// fallback (`interp::run_effect_serve`, the correctness oracle) produces. Boxed so
/// it does not bloat the common `Conn`; its `up_acc` heap allocation and boxed
/// sockaddr are pointer-stable across slab moves for the in-flight SQEs.
struct ProxyDial {
    /// The second socket to the upstream backend (shard-owned; created per dial,
    /// closed exactly once when the dial finishes — the copy-once/recycle discipline
    /// for the upstream fd).
    up_fd: RawFd,
    /// The proven-picked backend id (for the fleet success/failure breaker record).
    backend: u32,
    /// The request bytes to forward, produced by the proven core (`step[2..]`).
    forward_req: Vec<u8>,
    /// How many `forward_req` bytes have been written to the upstream so far.
    sent: usize,
    /// The accumulating upstream reply (grown by the recv loop). Recv SQEs land in
    /// its reserved tail; complete when [`ProxyDial::reply_complete`] says so.
    up_acc: Vec<u8>,
    /// The upstream sockaddr for the connect SQE (boxed for a stable address that
    /// outlives the in-flight connect op). Its length is passed by value into the
    /// connect SQE at dial start, so only the address itself needs to persist here.
    addr: Box<libc::sockaddr_storage>,
    /// Reply framing, decided once the head is complete.
    framing: ReplyFraming,
    /// Byte offset in `up_acc` of the end of the response head (`Some` once seen).
    head_end: Option<usize>,
    /// Incremental chunked-body parser (only advanced in the `Chunked` framing).
    chunk_parser: crate::proxy_dial::ChunkedParser,
    /// How many `up_acc` bytes have been fed to `chunk_parser` (feed the delta only).
    chunk_fed: usize,
    /// NATIVE RSS-BOUNDED PASSTHROUGH STREAMING (non-gzip, fixed `Content-Length`): once
    /// set, the transformed head has been sent and the body is forwarded straight through
    /// to the client, chunk by chunk, WITHOUT accumulating in `up_acc` — the body is never
    /// held whole. Byte-identical to the buffered `proxyRespTransform`
    /// (`Reactor.ServeStep.proxyStream_bytes_faithful`). gzip / chunked replies keep the
    /// buffered path (`stream` stays false).
    stream: bool,
    /// The body-byte target to forward while streaming (the upstream `Content-Length`).
    stream_target: usize,
    /// How many body bytes have been forwarded to the client so far while streaming.
    stream_forwarded: usize,
    /// Per-op UPSTREAM DEADLINE: the wall-clock instant by which the currently
    /// outstanding upstream op (connect / send / recv) must complete. Refreshed each
    /// time a fresh upstream SQE is armed ([`set_proxy_deadline`]), so a responsive
    /// upstream that keeps making progress is never affected — the deadline only
    /// elapses when the upstream HANGS (a connect that never lands, or a recv that
    /// never delivers a byte). [`sweep_proxy_timeouts`] fails a dial past its
    /// deadline: a 502 (still connecting / buffering the head) or a clean truncating
    /// close (mid-stream, head already sent), and recycles the upstream fd.
    op_deadline: Instant,
}

impl ProxyDial {
    /// Fold the currently-accumulated bytes and report whether the whole upstream
    /// reply has arrived. Decides the framing on first seeing the head (CRLFCRLF),
    /// then applies it: `Content-Length` ⇒ a target length, `chunked` ⇒ the
    /// incremental terminator parser, neither ⇒ close-delimited (never complete via
    /// bytes — only on EOF, handled by the recv completion). Mirrors
    /// `proxy_dial::read_response`'s framing, incrementally.
    fn reply_complete(&mut self) -> bool {
        if self.head_end.is_none() {
            match crate::proxy_dial::find(&self.up_acc, b"\r\n\r\n") {
                Some(p) => {
                    let he = p + 4;
                    self.head_end = Some(he);
                    let head = &self.up_acc[..he];
                    self.framing = if let Some(clen) = crate::proxy_dial::content_length(head) {
                        ReplyFraming::Fixed(he + clen)
                    } else if crate::proxy_dial::is_chunked(head) {
                        self.chunk_fed = he; // body starts at head_end
                        ReplyFraming::Chunked
                    } else {
                        ReplyFraming::Eof
                    };
                }
                None => return false, // head still incomplete
            }
        }
        match self.framing {
            ReplyFraming::Fixed(target) => self.up_acc.len() >= target,
            ReplyFraming::Chunked => {
                let done = self.chunk_parser.advance(&self.up_acc[self.chunk_fed..]);
                self.chunk_fed = self.up_acc.len();
                done
            }
            ReplyFraming::Eof | ReplyFraming::Unknown => false,
        }
    }

    /// The declared body length (`Content-Length`) for a fixed-framing reply — the total
    /// bytes to forward while streaming — else 0. `Fixed(target)` is the absolute
    /// accumulator length `head_end + Content-Length`, so the body length is
    /// `target - head_end`.
    fn stream_target_from_framing(&self) -> usize {
        match (self.framing, self.head_end) {
            (ReplyFraming::Fixed(target), Some(he)) => target.saturating_sub(he),
            _ => 0,
        }
    }
}

/// The parked continuation state for one in-flight effect-seam serve on the
/// io_uring shard — the async analogue of `interp::run_effect_serve`'s locals. It
/// carries the REPLAY byte-triple (`mask`, `req`, the GROWING `results` list) plus
/// the framing prefix and the resume seam, so each `submit_resume` re-crosses the
/// proven core with the identical `(prefix, mask, request, results)` the blocking
/// interpreter would. Boxed so it does not bloat the common (metered) `Conn`.
struct StepState {
    /// The framing prefix (LB-policy / selector byte) for this deployment, `None`
    /// on the default seam. Threaded on every step/resume, exactly as `interp`.
    prefix: Option<u8>,
    /// The live health/breaker bitmask the proven proxy pick reads (frozen at the
    /// step, as the blocking interpreter freezes it).
    mask: u8,
    /// The original request bytes — replayed on every resume (pure ⇒ deterministic).
    req: Vec<u8>,
    /// The recorded effect results, grown across resumes (the replay list).
    results: Vec<Vec<u8>>,
    /// The RESUME seam paired with the step seam this deployment dials with.
    resume_seam: Seam,
    /// Whether this connection's in-flight request wants keep-alive (captured at
    /// dispatch, applied when the final response is staged).
    keepalive: bool,
}

/// A free-list slab of connections (the `PendingSlab` shape: O(1)
/// insert/remove, slot reuse). One per shard.
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

/// Run `shards` io_uring shard threads over `listener_fd`, driving every request
/// through `gw`. `zc` selects the zero-copy receive/send path. Blocks until every
/// shard exits (on shutdown).
pub fn run(listener_fd: RawFd, gw: ServeGateway, shards: usize, zc: bool) {
    // The serve-owner set (`DRORB_SERVE_OWNERS`, default 1 = the original
    // single-owner model): each shard is PINNED to one owner, assigned
    // round-robin, so a shard's per-connection request/response FIFO order is
    // preserved while different shards' seam crossings overlap across owners.
    // Owner 0 is the primary runtime owner (the one `main` also hands to the
    // TLS/UDP/admin paths).
    let owners = crate::serve::serve_owner_set(gw);
    let mut handles = Vec::new();
    for id in 0..shards {
        let gw = owners[id % owners.len()].clone();
        handles.push(
            std::thread::Builder::new()
                .name(format!("drorb-shard-{id}"))
                .spawn(move || {
                    if let Err(e) = shard_loop(listener_fd, gw, zc) {
                        eprintln!("dataplane: shard {id} exited: {e}");
                    }
                })
                .expect("failed to spawn io_uring shard"),
        );
    }
    for h in handles {
        let _ = h.join();
    }
}

/// Everything a shard threads through its completion handlers.
struct Shard {
    gw: ServeGateway,
    efd: RawFd,
    mtx: Sender<ShardDone>,
    slab: Slab,
    backlog: Vec<squeue::Entry>,
    /// Whether this shard runs the zero-copy receive/send path.
    zc: bool,
    /// The provided-buffer ring, present only in zero-copy mode.
    br: Option<BufRing>,
    /// How many connections currently hold an in-flight NATIVE proxy dial
    /// (`conn.proxy.is_some()`). Nonzero ⇒ the shard waits with a bounded
    /// [`PROXY_SWEEP_NS`] timeout so it can sweep upstream deadlines; zero ⇒ the
    /// shard blocks indefinitely on completions (no wasted wakeups on the hot path).
    /// Incremented when a dial is parked ([`start_proxy_dial`]), decremented wherever
    /// the dial's `proxy` box is taken ([`take_proxy`]).
    proxy_inflight: u32,
    /// Landing sockaddr for the single in-flight accept: the kernel writes the
    /// connecting peer's address here on each accept completion, and the metered
    /// path reads it as the connection's client IP. Boxed so its address is stable
    /// across `Shard` moves and outlives every in-flight accept op. Exactly one
    /// accept is in flight per shard (each `on_accept` re-arms one), so one buffer
    /// suffices; the paired `accept_addrlen` is the sockaddr's in/out length.
    accept_addr: Box<libc::sockaddr_storage>,
    accept_addrlen: Box<libc::socklen_t>,
    /// Per-source STANDING connection counters, shard-local (no lock): the
    /// accept-path state the sans-IO serve fold cannot carry. Incremented at
    /// `on_accept`, decremented at `close` — exactly once each — and consulted at
    /// accept to enforce the config's `max-connections` cap (the proven
    /// `Reactor.Stage.ConnLimit` decision, `Reactor/StandingCounters.lean`).
    standing: crate::standing::Standing,
}

/// Decode the accept sockaddr the kernel filled into a client `IpAddr`. Unknown
/// families fall back to the unspecified IPv4 address (which the default-admit
/// IP-filter ruleset passes), matching `blocking`'s unresolvable-peer fallback.
fn peer_ip_from_storage(ss: &libc::sockaddr_storage) -> IpAddr {
    match ss.ss_family as i32 {
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

/// One shard: its own ring, eventfd, connection slab, and serve mailbox.
fn shard_loop(listener_fd: RawFd, gw: ServeGateway, zc: bool) -> std::io::Result<()> {
    let mut ring: IoUring = IoUring::new(RING_ENTRIES)?;

    // The provided-buffer ring (zero-copy receive). Registered against this
    // shard's ring; the two hold disjoint memory and outlive every in-flight op.
    // If registration fails (old kernel without buf_ring), fall back to the plain
    // pooled-recv path rather than aborting the shard.
    let (zc, br) = if zc {
        match BufRing::new(&ring.submitter(), BR_BGID, BR_ENTRIES, RECV_CHUNK) {
            Ok(br) => (true, Some(br)),
            Err(e) => {
                eprintln!(
                    "dataplane: buf_ring unavailable ({e}); shard falls back to plain recv/send"
                );
                (false, None)
            }
        }
    } else {
        (false, None)
    };

    // eventfd for serve-completion wakeups from the runtime-owner thread.
    // SAFETY: eventfd(2) with a zero initial count and valid flags; the returned
    // fd is checked and owned by this shard until the process exits.
    let efd = unsafe { libc::eventfd(0, libc::EFD_CLOEXEC | libc::EFD_NONBLOCK) };
    if efd < 0 {
        return Err(std::io::Error::last_os_error());
    }

    let (mtx, mrx): (Sender<ShardDone>, Receiver<ShardDone>) = channel();
    // SAFETY: an all-zero `sockaddr_storage` is a valid (empty) address; the kernel
    // overwrites it on each accept completion.
    let mut sh = Shard {
        gw,
        efd,
        mtx,
        slab: Slab::new(),
        backlog: Vec::new(),
        zc,
        br,
        proxy_inflight: 0,
        accept_addr: Box::new(unsafe { std::mem::zeroed() }),
        accept_addrlen: Box::new(std::mem::size_of::<libc::sockaddr_storage>() as libc::socklen_t),
        standing: crate::standing::Standing::new(),
    };
    // Stable 8-byte target for the eventfd read; its address must outlive each
    // in-flight read op, so the loop owns it for its whole lifetime.
    let mut efd_buf: u64 = 0;

    // Prime the ring: one accept on the shared listener (its sockaddr landing the
    // peer address for the metered path), one eventfd read.
    let addr_ptr = sh.accept_addr.as_mut() as *mut libc::sockaddr_storage;
    let len_ptr = sh.accept_addrlen.as_mut() as *mut libc::socklen_t;
    sh.backlog.push(accept_sqe(listener_fd, addr_ptr, len_ptr));
    sh.backlog.push(eventfd_sqe(efd, &mut efd_buf));

    // Bound the per-source rate-window map: reclaim entries whose window has fully
    // elapsed (idle sources leave no residue), at most once per window so it never
    // grows without limit under a many-source flood. Local to the loop — no shard
    // field, no hot-path cost when rate limiting is disabled.
    let mut last_rate_prune = Instant::now();

    loop {
        flush(&mut ring, &mut sh.backlog)?;
        // Wait for at least one completion. While a NATIVE proxy dial is outstanding,
        // cap the wait at PROXY_SWEEP_NS so the shard wakes to sweep upstream
        // deadlines even if the hung upstream posts nothing (submit_with_args returns
        // ETIME on that cap — a benign sweep tick, handled like a spurious wake). With
        // no dial in flight the shard blocks indefinitely (no hot-path wakeups).
        let waited = if sh.proxy_inflight > 0 {
            let ts = types::Timespec::new().nsec(PROXY_SWEEP_NS);
            let args = types::SubmitArgs::new().timespec(&ts);
            ring.submitter().submit_with_args(1, &args)
        } else {
            ring.submit_and_wait(1)
        };
        match waited {
            Ok(_) => {}
            // Timeout cap elapsed with fewer than `want` completions: fall through to
            // reap whatever DID arrive, then sweep the upstream deadlines.
            Err(ref e) if e.raw_os_error() == Some(libc::ETIME) => {}
            Err(ref e) if e.raw_os_error() == Some(libc::EINTR) => {
                if crate::SHUTDOWN.load(Ordering::SeqCst) {
                    return Ok(());
                }
                continue;
            }
            Err(e) => return Err(e),
        }

        // Reap this batch. Copy out (user_data, result, flags) so the completion
        // borrow is released before we push new SQEs. `flags` carries the buf_ring
        // buffer id (recv) and the zero-copy notification bit (send).
        let batch: Vec<(u64, i32, u32)> = ring
            .completion()
            .map(|c| (c.user_data(), c.result(), c.flags()))
            .collect();

        for (ud, res, flags) in batch {
            let slot = (ud & SLOT_MASK) as u32;
            match ud & TAG_MASK {
                TAG_ACCEPT => on_accept(&mut sh, res, listener_fd),
                TAG_EVENTFD => on_wakeup(&mut sh, &mrx, &mut efd_buf),
                TAG_RECV => on_recv(&mut sh, slot, res),
                TAG_RECV_BR => on_recv_br(&mut sh, slot, res, flags),
                TAG_SEND => on_send(&mut sh, slot, res, flags),
                TAG_PROXY_CONNECT => on_proxy_connect(&mut sh, slot, res),
                TAG_PROXY_SEND => on_proxy_send(&mut sh, slot, res),
                TAG_PROXY_RECV => on_proxy_recv(&mut sh, slot, res),
                TAG_CLOSE => {} // fire-and-forget; the slot was freed at submit time
                _ => {}
            }
        }

        // Fail any NATIVE proxy dial whose outstanding upstream op blew its deadline
        // (a hung upstream) — 502 + upstream-fd recycle. Reap-before-sweep: a dial
        // whose recv/connect just completed in this batch already had its `proxy`
        // taken above, so it is not re-swept.
        sweep_proxy_timeouts(&mut sh);

        // Reclaim idle rate-window entries (bounded growth), throttled to once per
        // window. Cheap no-op when rate limiting is off.
        if crate::config::rate_limit() != 0 {
            let now = Instant::now();
            let window = crate::config::rate_window();
            if now.duration_since(last_rate_prune) >= window {
                sh.standing.rate_prune(window, now);
                last_rate_prune = now;
            }
        }

        if crate::SHUTDOWN.load(Ordering::SeqCst) {
            return Ok(());
        }
    }
}

// --- SQE builders ---------------------------------------------------------

/// Build an accept SQE whose completion lands the connecting peer's address in
/// `*addr` (the metered path's client IP). `addrlen` is reset to the full storage
/// size first (the kernel reads it as the in/out buffer capacity). Both pointers
/// name the shard's boxed accept buffers, which outlive the in-flight op; exactly
/// one accept is in flight per shard, so the single buffer is never aliased.
fn accept_sqe(
    listener_fd: RawFd,
    addr: *mut libc::sockaddr_storage,
    addrlen: *mut libc::socklen_t,
) -> squeue::Entry {
    // SAFETY: `addrlen` is the shard's live boxed `socklen_t`; reset it to the
    // buffer capacity before each accept, as the accept(2) in/out contract requires.
    unsafe {
        *addrlen = std::mem::size_of::<libc::sockaddr_storage>() as libc::socklen_t;
    }
    opcode::Accept::new(types::Fd(listener_fd), addr as *mut libc::sockaddr, addrlen)
        .build()
        .user_data(TAG_ACCEPT)
}

fn eventfd_sqe(efd: RawFd, buf: &mut u64) -> squeue::Entry {
    opcode::Read::new(types::Fd(efd), buf as *mut u64 as *mut u8, 8)
        .build()
        .user_data(TAG_EVENTFD)
}

/// Reserve receive space at the tail of `conn.acc` and build a plain recv SQE that
/// fills it. The pointer is into `acc`'s heap allocation, which is stable across
/// slab moves (the `Vec` control block may move; the allocation it points to does
/// not), so the in-flight op stays valid until its completion.
fn recv_sqe(conn: &mut Conn, slot: u32) -> squeue::Entry {
    conn.acc.reserve(RECV_CHUNK);
    let len = conn.acc.len();
    // SAFETY: `reserve` guaranteed capacity for RECV_CHUNK bytes past `len`; the
    // pointer is valid for that many bytes and the kernel initializes them.
    let ptr = unsafe { conn.acc.as_mut_ptr().add(len) };
    opcode::Recv::new(types::Fd(conn.fd), ptr, RECV_CHUNK as u32)
        .build()
        .user_data(TAG_RECV | slot as u64)
}

/// Build a buffer-select recv SQE that draws its landing buffer from the
/// provided-buffer ring (group `BR_BGID`). The kernel picks a free slot and
/// reports its id in the completion flags.
fn recv_br_sqe(fd: RawFd, slot: u32) -> squeue::Entry {
    opcode::Recv::new(types::Fd(fd), std::ptr::null_mut(), RECV_CHUNK as u32)
        .buf_group(BR_BGID)
        .build()
        .flags(squeue::Flags::BUFFER_SELECT)
        .user_data(TAG_RECV_BR | slot as u64)
}

/// Build a send SQE for the unsent tail of `conn.resp`. In zero-copy mode this is
/// `SendZc` straight from the response bytes (which the caller keeps alive until
/// the notification); otherwise a plain copying `Send`.
fn send_sqe(conn: &Conn, slot: u32, zc: bool) -> squeue::Entry {
    let resp = conn.resp.as_ref().expect("send with no response staged");
    let ptr = resp[conn.sent..].as_ptr();
    let len = (resp.len() - conn.sent) as u32;
    if zc {
        opcode::SendZc::new(types::Fd(conn.fd), ptr, len)
            .build()
            .user_data(TAG_SEND | slot as u64)
    } else {
        opcode::Send::new(types::Fd(conn.fd), ptr, len)
            .build()
            .user_data(TAG_SEND | slot as u64)
    }
}

fn close_sqe(fd: RawFd) -> squeue::Entry {
    opcode::Close::new(types::Fd(fd))
        .build()
        .user_data(TAG_CLOSE)
}

/// Arm the next receive for `slot`: a buffer-select recv in zero-copy mode, else
/// a plain pooled recv into the accumulation buffer.
fn arm_recv(sh: &mut Shard, slot: u32) {
    let zc = sh.zc;
    let sqe = match sh.slab.get(slot) {
        Some(conn) => {
            if zc {
                recv_br_sqe(conn.fd, slot)
            } else {
                recv_sqe(conn, slot)
            }
        }
        None => return,
    };
    sh.backlog.push(sqe);
}

/// Arm one send op for `slot`, counting it against the zero-copy notification
/// bookkeeping.
fn push_send(sh: &mut Shard, slot: u32) {
    let zc = sh.zc;
    let sqe = match sh.slab.get(slot) {
        Some(conn) => {
            if zc {
                conn.zc_issued += 1;
            }
            send_sqe(conn, slot, zc)
        }
        None => return,
    };
    sh.backlog.push(sqe);
}

// --- completion handlers --------------------------------------------------

fn on_accept(sh: &mut Shard, res: i32, listener_fd: RawFd) {
    // Read the peer address the kernel wrote for THIS accept BEFORE re-arming (the
    // re-arm reuses the same sockaddr buffer). Valid only for a successful accept;
    // on error we return before it is used.
    let peer_ip = peer_ip_from_storage(&sh.accept_addr);
    // Always re-arm accept so the shard keeps taking new connections.
    let addr_ptr = sh.accept_addr.as_mut() as *mut libc::sockaddr_storage;
    let len_ptr = sh.accept_addrlen.as_mut() as *mut libc::socklen_t;
    sh.backlog.push(accept_sqe(listener_fd, addr_ptr, len_ptr));
    if res < 0 {
        return; // transient accept error (e.g. EMFILE); the re-arm retries
    }
    let fd = res as RawFd;
    if sh.slab.live() >= MAX_CONNS_PER_SHARD {
        sh.backlog.push(close_sqe(fd)); // at the shard cap: refuse
        return;
    }
    // REACTOR-LEVEL per-source connection-limit gate — the accept-path STANDING
    // state (`conn-active`) the sans-IO serve fold cannot carry. Read the source's
    // CURRENT active-connection count BEFORE this connection's own increment; the
    // proven admission rule decides (`Reactor.Stage.ConnLimit.admits`: cap 0 =
    // unlimited, else admit iff active < cap).
    let now = Instant::now();
    let cap = crate::config::max_connections();
    let over_limit = cap != 0 && sh.standing.active(peer_ip) >= cap;
    // Count this connection: EXACTLY ONE increment per conn entering the slab,
    // matched by EXACTLY ONE decrement at `close` — the conn_conservation
    // discipline proven in `Reactor/StandingCounters.lean`. Refused conns are
    // counted too (they still enter the slab and close through the same funnel),
    // so the accounting stays symmetric on every path.
    sh.standing.on_accept(peer_ip);
    // REACTOR-LEVEL per-source REQUEST-RATE gate — note this arrival against the
    // source's sliding window (`rate_note` ages the window and counts it, lock-free
    // on this shard thread). Over the `rate-limit` cap ⇒ answer the REAL `429` and
    // close WITHOUT dispatching (`rate_limit_fires`, `Reactor/StandingCounters.lean`).
    // A disabled cap (`0`) never fires — the unlimited default. Precedence: the
    // connection-resource `503` first, then the request-rate `429`.
    let over_rate = sh.standing.rate_note(
        peer_ip,
        crate::config::rate_limit(),
        crate::config::rate_window(),
        now,
    );
    let conn = Conn {
        fd,
        peer_ip,
        conn_seq: 0,
        acc: sh.gw.pool().take(),
        leased_bid: None,
        resp: None,
        sent: 0,
        zc_issued: 0,
        zc_data: 0,
        zc_notif_exp: 0,
        zc_notif: 0,
        zc_error: false,
        req_keepalive: false,
        keepalive: false,
        h2c: false,
        step: None,
        proxy: None,
        awaiting_stream_head: false,
        req_start: now,
        logrec: None,
        stream_head: None,
        hdr_start: now,
        headers_done: false,
        req_len: 0,
        split: None,
    };
    let slot = sh.slab.insert(conn);
    if over_limit {
        // At/over the per-source cap: answer the REAL `503` and close WITHOUT
        // dispatching to the serve (the handler and every serve stage are skipped).
        // io_uring accepts complete after the TCP handshake, so the shard owns the
        // socket and writes a genuine 503 body; `stage_response` leaves keepalive
        // false (req_keepalive defaults false), so the connection is torn down after
        // the send and `close` decrements the counter exactly once.
        REFUSED_503.fetch_add(1, Ordering::Relaxed);
        let mut resp = sh.gw.pool().take();
        resp.extend_from_slice(CONN_LIMIT_503);
        stage_response(sh, slot, resp, false);
    } else if over_rate {
        // Over the per-source request-rate window: answer the REAL `429` and close
        // WITHOUT dispatching. Same teardown funnel as the `503` (keepalive false ⇒
        // `close` decrements the standing counter exactly once).
        REFUSED_429.fetch_add(1, Ordering::Relaxed);
        let mut resp = sh.gw.pool().take();
        resp.extend_from_slice(RATE_LIMIT_429);
        stage_response(sh, slot, resp, false);
    } else {
        arm_recv(sh, slot);
    }
}

fn on_wakeup(sh: &mut Shard, mrx: &Receiver<ShardDone>, efd_buf: &mut u64) {
    // Drain every completed response (coalesced eventfd counts may batch them).
    while let Ok(done) = mrx.try_recv() {
        // PHASE 0 effect seam: a connection with a STEP/RESUME in flight receives an
        // encoded `Step`, NOT a final response. Decode it, run the in-memory effect,
        // and drive the next resume (or stage the `.done` bytes / defer). The lease
        // recycle + response staging below is the default (metered) path.
        // A connection awaiting the CL-trust STREAMING HEAD receives the transformed
        // head (or empty on gzip), NOT a `Step` — route it to the streaming driver.
        if sh
            .slab
            .get(done.conn)
            .map(|c| c.awaiting_stream_head)
            .unwrap_or(false)
        {
            on_stream_head_reply(sh, done.conn, done.resp);
            continue;
        }
        if sh
            .slab
            .get(done.conn)
            .map(|c| c.step.is_some())
            .unwrap_or(false)
        {
            on_step_reply(sh, done.conn, done.resp);
            continue;
        }
        stage_response(sh, done.conn, done.resp, done.split_static);
    }
    sh.backlog.push(eventfd_sqe(sh.efd, efd_buf));
}

/// Stage a FINAL response for `slot` and arm its send — the default metered path,
/// and the effect seam's `.done` / deferred-fallback path. Recycles any held
/// receive lease exactly once (`Uring.recycle_at_most_once`), records the
/// keep-alive disposition, annotates the `Connection:` header for HTTP/1.1, and
/// pushes the send.
fn stage_response(sh: &mut Shard, slot: u32, resp: PooledBuf, split_static: bool) {
    // ZERO-COPY STATIC BODY (`DRORB_SPAN=23`): the serve thread returned a HEAD-only
    // response whose (constant) body is the process-static buffer — gather-write head
    // + static body via `writev`; the body is never copied per request.
    if split_static {
        return stage_static_split_response(sh, slot, resp);
    }
    // ZERO-COPY BODY (`DRORB_SPAN=15`): when the split seam is active AND this request
    // was borrowed into a still-held lease, `resp` is the response HEAD ONLY (no body
    // append). Write head THEN the borrowed body via `writev`, splicing the body from
    // the held lease slot — never appended into an output buffer. Requires the lease
    // (the body source) and a non-empty request; otherwise fall through (the head-only
    // resp cannot be completed on a non-borrow path — send the head and close).
    if crate::serve::is_split_span() {
        let can_split = sh
            .slab
            .get(slot)
            .map(|c| c.leased_bid.is_some() && c.req_len > 0 && sh.br.is_some())
            .unwrap_or(false);
        if can_split {
            return stage_split_response(sh, slot, resp);
        }
        // Split seam active but the request was NOT borrowed into a single held slot
        // (it spanned multiple recvs — a body larger than one `RECV_CHUNK` (16 KiB) — or
        // arrived pipelined, so it was accumulated and drained from `acc`). `resp` is the
        // HEAD ONLY; there is no retained body to splice. FAIL SAFE: close the connection
        // rather than ship a truncated response. (The zero-copy-body split measurement
        // drives ≤16 KiB requests, which take the single-slot borrow path.)
        return close(sh, slot);
    }
    stage_response_appended(sh, slot, resp);
}

/// The default (appended) response staging: recycle the held lease, annotate the
/// connection disposition, record metrics/access-log, and arm the single copying send.
fn stage_response_appended(sh: &mut Shard, slot: u32, mut resp: PooledBuf) {
    // Recycle the leased receive buffer now that the request has been served (the
    // serve thread finished reading it before posting this response).
    let bid = sh.slab.get(slot).and_then(|c| c.leased_bid.take());
    if let (Some(bid), Some(br)) = (bid, sh.br.as_mut()) {
        br.recycle(bid);
        ZC_RECYCLE.fetch_add(1, Ordering::Relaxed);
    }
    // REAL GZIP SEAM (`DRORB_RUST_GZIP=1`): replace the proven stored-block gzip
    // stage's (uncompressed) body with real flate2 DEFLATE. Keyed on the response's
    // own `Content-Encoding: gzip`; inert when the flag is unset or the response was
    // not gzipped. Runs BEFORE keepalive detection so the rewritten Content-Length is
    // what decides self-delimitation. (Trusted, not verified.)
    if crate::gzip::enabled() {
        crate::gzip::recompress(&mut resp);
    }
    if let Some(conn) = sh.slab.get(slot) {
        conn.keepalive = !conn.h2c && conn.req_keepalive && response_is_self_delimited(&resp);
        // State the connection disposition explicitly for strict HTTP/1.1 clients
        // (never on raw h2c frames — they carry no HTTP/1.1 head).
        if !conn.h2c {
            crate::http::annotate_connection(&mut resp, conn.keepalive);
        }
        // OBSERVABILITY (mirrors `blocking::handle_conn`'s post-serve `emit`): count
        // this served response and write its access-log line, ONCE, at the point it is
        // finalized for send — the funnel every buffered response (default metered,
        // config, braid, and effect-`.done` incl. buffered proxy) passes through.
        // Skipped for raw h2c frames, exactly as blocking's h2c path emits nothing.
        // `backend = None`: the metered and effect-done paths record None, as blocking
        // does (`emit(&resp, None)`); a proxied response's backend counter is bumped by
        // the fleet, not here.
        if !conn.h2c {
            crate::metrics::record(&resp, None);
            if let Some((rl, client)) = &conn.logrec {
                crate::access_log::log(*client, rl, &resp, None, conn.req_start);
            }
        }
        conn.resp = Some(resp);
        conn.sent = 0;
        conn.zc_issued = 0;
        conn.zc_data = 0;
        conn.zc_notif_exp = 0;
        conn.zc_notif = 0;
        conn.zc_error = false;
    } else {
        // Connection already gone; drop the response (returns to the pool).
        return;
    }
    push_send(sh, slot);
}

/// ZERO-COPY BODY (`DRORB_SPAN=15`) response staging: `head` is the Lean-computed
/// response HEAD (no body append). Annotate the connection disposition on the head,
/// record metrics/access-log, then arm a `writev` gathering the head and the borrowed
/// body — the whole request bytes STILL in the held lease slot (`leased_bid`,
/// `req_len`). The body is sliced from the buf_ring at send time and gathered by the
/// kernel; it is NEVER appended into an output `ByteArray`. The lease is held (not
/// recycled here) until the split send completes, then recycled exactly once.
fn stage_split_response(sh: &mut Shard, slot: u32, mut head: PooledBuf) {
    let (body_bid, body_len) = {
        let conn = match sh.slab.get(slot) {
            Some(c) => c,
            None => return,
        };
        // The head is self-delimited (Lean baked in Content-Length = req_len); keep-alive
        // follows the request's intent, exactly as the appended path.
        conn.keepalive = !conn.h2c && conn.req_keepalive && response_is_self_delimited(&head);
        if !conn.h2c {
            crate::http::annotate_connection(&mut head, conn.keepalive);
        }
        if !conn.h2c {
            // The metrics/log read the head's status + Content-Length (both present); the
            // body is not in `head`, but neither field needs it.
            crate::metrics::record(&head, None);
            if let Some((rl, client)) = &conn.logrec {
                crate::access_log::log(*client, rl, &head, None, conn.req_start);
            }
        }
        // The held lease slot (its bid) is the body source; keep it LEASED across the
        // send (do not `take` it) — recycled once the split send fully settles.
        let bid = match conn.leased_bid {
            Some(b) => b,
            None => return, // guarded by can_split; defensive
        };
        (bid, conn.req_len)
    };
    if let Some(conn) = sh.slab.get(slot) {
        conn.split = Some(Box::new(SplitSend {
            head,
            body: SplitBody::Lease(body_bid),
            body_len,
            sent: 0,
            iov: [libc::iovec {
                iov_base: std::ptr::null_mut(),
                iov_len: 0,
            }; 2],
            iov_n: 0,
        }));
    } else {
        return;
    }
    push_split_send(sh, slot);
}

/// ZERO-COPY STATIC BODY (`DRORB_SPAN=23`) response staging: `head` is the fused
/// response HEAD (no body); the body is the process-static constant buffer. Recycle
/// any held receive lease now (the body does NOT come from it — mirrors the appended
/// path), annotate the connection disposition on the head, record metrics/access-log,
/// then arm a `writev` gathering the head and the static body — the body rides by
/// pointer, copied by nobody in userspace.
fn stage_static_split_response(sh: &mut Shard, slot: u32, mut head: PooledBuf) {
    // The request's receive lease (if any) is done with: the request has been served
    // and the body source is static. Recycle exactly once, as the appended path does.
    let bid = sh.slab.get(slot).and_then(|c| c.leased_bid.take());
    if let (Some(bid), Some(br)) = (bid, sh.br.as_mut()) {
        br.recycle(bid);
        ZC_RECYCLE.fetch_add(1, Ordering::Relaxed);
    }
    let body: &'static [u8] = crate::serve::static_bulk_body();
    if let Some(conn) = sh.slab.get(slot) {
        // The head is self-delimited (Content-Length baked in); keep-alive follows
        // the request's intent, exactly as the appended path.
        conn.keepalive = !conn.h2c && conn.req_keepalive && response_is_self_delimited(&head);
        if !conn.h2c {
            crate::http::annotate_connection(&mut head, conn.keepalive);
        }
        if !conn.h2c {
            // The metrics/log read the head's status + Content-Length (both present).
            crate::metrics::record(&head, None);
            if let Some((rl, client)) = &conn.logrec {
                crate::access_log::log(*client, rl, &head, None, conn.req_start);
            }
        }
        conn.split = Some(Box::new(SplitSend {
            head,
            body: SplitBody::Static(body),
            body_len: body.len(),
            sent: 0,
            iov: [libc::iovec {
                iov_base: std::ptr::null_mut(),
                iov_len: 0,
            }; 2],
            iov_n: 0,
        }));
    } else {
        return;
    }
    push_split_send(sh, slot);
}

/// Build the `writev` SQE for the unsent remainder of a split send: the unsent head
/// bytes (if any) followed by the body sliced from the held lease slot. Fills the
/// connection's kept-alive `iov` gather array (so it outlives the in-flight SQE) and
/// returns the `writev` entry. TAG_SEND so `on_send` routes it (via `conn.split`).
fn split_send_sqe(sh: &mut Shard, slot: u32) -> Option<squeue::Entry> {
    // The body base pointer: sliced from the registered buf_ring memory (stable while
    // the lease is held) or the process-static buffer (stable forever). Computed
    // first, then released before the mutable `conn` borrow.
    enum Src {
        Lease(u16, usize),
        Static(*const u8),
    }
    let src = {
        let conn = sh.slab.get(slot)?;
        let sp = conn.split.as_ref()?;
        match sp.body {
            SplitBody::Lease(bid) => Src::Lease(bid, sp.body_len),
            SplitBody::Static(s) => Src::Static(s.as_ptr()),
        }
    };
    let body_base = match src {
        // SAFETY: `bid` is the still-held lease; `body_len` bytes were received into
        // it. The registered buffer memory is stable until the lease is recycled
        // (after this send settles), so the pointer is valid for the writev's lifetime.
        Src::Lease(bid, len) => {
            (unsafe { sh.br.as_ref()?.slice(bid, len).as_ptr() }) as *mut libc::c_void
        }
        // The process-static body: valid for the process lifetime.
        Src::Static(p) => p as *mut libc::c_void,
    };
    let conn = sh.slab.get(slot)?;
    let fd = conn.fd;
    let sp = conn.split.as_mut()?;
    let head_len = sp.head.len();
    let total = head_len + sp.body_len;
    if sp.sent >= total {
        return None;
    }
    let mut n = 0usize;
    if sp.sent < head_len {
        // SAFETY: the head buffer is kept alive in `sp.head` for the SQE's lifetime.
        let hptr = unsafe { sp.head.as_ptr().add(sp.sent) } as *mut libc::c_void;
        sp.iov[n] = libc::iovec {
            iov_base: hptr,
            iov_len: head_len - sp.sent,
        };
        n += 1;
        sp.iov[n] = libc::iovec {
            iov_base: body_base,
            iov_len: sp.body_len,
        };
        n += 1;
    } else {
        let off = sp.sent - head_len;
        // SAFETY: `off < body_len`; the slot is leased for the SQE's lifetime.
        let bptr = unsafe { body_base.add(off) };
        sp.iov[n] = libc::iovec {
            iov_base: bptr,
            iov_len: sp.body_len - off,
        };
        n += 1;
    }
    sp.iov_n = n as u32;
    let iov_ptr = sp.iov.as_ptr();
    Some(
        // offset -1 (u64::MAX): the fd is a stream socket (non-seekable), so no file
        // offset applies — writev-to-socket = a gather write of head then body.
        opcode::Writev::new(types::Fd(fd), iov_ptr, n as u32)
            .offset(u64::MAX)
            .build()
            .user_data(TAG_SEND | slot as u64),
    )
}

/// Arm (or re-arm) the split send's `writev` for `slot`.
fn push_split_send(sh: &mut Shard, slot: u32) {
    if let Some(sqe) = split_send_sqe(sh, slot) {
        sh.backlog.push(sqe);
    }
}

/// Completion of a split-send `writev` (`DRORB_SPAN=15`). Advance the acknowledged
/// count; on a short write re-arm the remainder, otherwise recycle the held lease
/// (exactly once), release the head, and continue/close the connection.
fn on_split_send(sh: &mut Shard, slot: u32, res: i32) {
    if res <= 0 {
        return close(sh, slot);
    }
    let done = {
        let conn = match sh.slab.get(slot) {
            Some(c) => c,
            None => return,
        };
        let sp = match conn.split.as_mut() {
            Some(s) => s,
            None => return,
        };
        sp.sent += res as usize;
        sp.sent >= sp.head.len() + sp.body_len
    };
    if !done {
        return push_split_send(sh, slot);
    }
    // Whole response (head + body) written. Recycle the body's lease exactly once.
    let bid = sh.slab.get(slot).and_then(|c| c.leased_bid.take());
    if let (Some(bid), Some(br)) = (bid, sh.br.as_mut()) {
        br.recycle(bid);
        ZC_RECYCLE.fetch_add(1, Ordering::Relaxed);
    }
    let keepalive = match sh.slab.get(slot) {
        Some(conn) => {
            conn.split = None; // the head buffer returns to the pool here
            conn.keepalive
        }
        None => return,
    };
    finish_send(sh, slot, keepalive);
}

/// PHASE 0 effect-seam driver: decode one encoded `Step` reply for `slot` (its
/// `step` state is in flight) and drive the async continuation. This is the io_uring
/// interpreter — the async, non-blocking analogue of `interp::run_effect_serve`'s
/// loop body, over the SAME encoded `Step` tags and the SAME replay contract:
///
///   * `TAG_DONE` — the serve produced the full response; stage it and send.
///   * `cacheLookup` / `cacheStore` — the NON-BLOCKING in-memory cache effects:
///     execute inline against `cache::global()`, append the recorded result, and
///     `submit_resume` immediately (the loop is the eventfd wakeup itself).
///   * a cold-key WAITER, the DISK cache tier, and `proxyDial` — the BLOCKING /
///     SQE-driven effects: DEFER this one request to a blocking fallback thread
///     (Phase 1/2 lower them onto the SQE path). The shard itself never blocks.
fn on_step_reply(sh: &mut Shard, slot: u32, step: PooledBuf) {
    match step.first().copied() {
        // The serve is DONE: the rest is the full response. Clear the step state and
        // stage it on the normal send path.
        Some(crate::interp::TAG_DONE) => {
            if let Some(conn) = sh.slab.get(slot) {
                // Carry the captured keep-alive intent onto the final send.
                if let Some(st) = conn.step.take() {
                    conn.req_keepalive = st.keepalive;
                }
            }
            let mut resp = sh.gw.pool().take();
            resp.extend_from_slice(&step[1..]);
            stage_response(sh, slot, resp, false);
        }

        // YIELD cacheLookup: the NON-BLOCKING in-memory probe. A fresh HIT or a
        // cold-key LEADER resumes inline; a WAITER (a leader is already in flight)
        // or the durable DISK tier is deferred (both would block the shard).
        Some(crate::interp::TAG_YIELD_CACHE_LOOKUP) => {
            if crate::cache_disk::global().enabled() {
                // DISK cache (DRORB_DISK_CACHE) consult is blocking file I/O —
                // Phase 1. Defer this whole request to the blocking fallback.
                return defer_to_blocking(sh, slot);
            }
            let probe = crate::cache::global().lookup_effect_nb(&step[1..]);
            match probe {
                CacheProbe::Hit(hit) => {
                    push_result_and_resume(sh, slot, hit);
                }
                CacheProbe::Leader => {
                    // The cold-key leader: resume with an empty result; the core runs
                    // the fold once, then yields cacheStore (which publishes to
                    // waiters). Exactly `interp::run_effect_serve`'s leader arm.
                    push_result_and_resume(sh, slot, Vec::new());
                }
                CacheProbe::Waiter => {
                    // A leader is already in flight for this key; coalescing waits on
                    // its condvar (blocking). Defer this one request off the shard.
                    defer_to_blocking(sh, slot);
                }
            }
        }

        // YIELD cacheStore: the NON-BLOCKING in-memory store. With the disk tier off
        // this is a pure map insert (+ publishing to any coalesced waiters), so run
        // it inline and resume. With the disk tier on the store ALSO writes the
        // durable tier (blocking) — defer that request (Phase 1).
        Some(crate::interp::TAG_YIELD_CACHE_STORE) if step.len() >= 9 => {
            if crate::cache_disk::global().enabled() {
                return defer_to_blocking(sh, slot);
            }
            let lifetime = u32::from_be_bytes([step[1], step[2], step[3], step[4]]) as u64;
            let key_len = u32::from_be_bytes([step[5], step[6], step[7], step[8]]) as usize;
            let key_end = 9 + key_len;
            if step.len() < key_end {
                return defer_to_blocking(sh, slot);
            }
            crate::cache::global().store(&step[9..key_end], &step[key_end..], lifetime);
            // The store ack the core ignores.
            push_result_and_resume(sh, slot, Vec::new());
        }

        // YIELD proxyDial (network I/O): the NATIVE second-socket SQE path. The
        // proven core chose the backend (`step[1]`) and produced the forward request
        // (`step[2..]`); the shard dials it on a SECOND socket via connect → send →
        // recv-loop SQEs (never blocking), accumulates the upstream reply, and
        // threads it into `submit_resume` — realizing `Reactor.DriveProxy`'s
        // `drive_proxy_refines`/`drive_proxy_stream_refines`. With
        // `DRORB_PROXY_BLOCKING=1` (or a too-short frame) this falls to the blocking
        // fallback below instead. Never fakes the effect; never blocks the shard.
        Some(crate::interp::TAG_YIELD_PROXY) if step.len() >= 2 && native_proxy_enabled() => {
            let backend = step[1] as u32;
            let forward_req = step[2..].to_vec();
            start_proxy_dial(sh, slot, backend, forward_req);
        }

        // A disk/store frame too short, an unrecognized tag, or proxy with the
        // blocking fallback forced: DEFER to the blocking fallback. Never fake the
        // effect as done, never block the shard.
        _ => defer_to_blocking(sh, slot),
    }
}

/// Whether the NATIVE second-socket SQE proxy path drives `proxyDial` on the shard
/// (the default), or the request is DEFERRED to the blocking fallback thread. Set
/// `DRORB_PROXY_BLOCKING=1` to force the fallback (the safety net). Read once.
fn native_proxy_enabled() -> bool {
    use std::sync::OnceLock;
    static NATIVE: OnceLock<bool> = OnceLock::new();
    *NATIVE.get_or_init(|| {
        !std::env::var("DRORB_PROXY_BLOCKING")
            .map(|v| matches!(v.as_str(), "1" | "true" | "yes" | "on"))
            .unwrap_or(false)
    })
}

/// The per-op UPSTREAM DEADLINE budget: how long one upstream op (connect / send /
/// recv) may take before the dial is failed as hung. `DRORB_PROXY_TIMEOUT_MS`
/// overrides the 5 s default; a zero/unparseable value keeps the default. Read once.
fn proxy_timeout() -> Duration {
    use std::sync::OnceLock;
    static T: OnceLock<Duration> = OnceLock::new();
    *T.get_or_init(|| {
        let ms = std::env::var("DRORB_PROXY_TIMEOUT_MS")
            .ok()
            .and_then(|v| v.parse::<u64>().ok())
            .filter(|&m| m > 0)
            .unwrap_or(5000);
        Duration::from_millis(ms)
    })
}

/// (Re)arm the upstream deadline to one [`proxy_timeout`] budget from now. Called at
/// every point a fresh upstream SQE is armed (connect, send, each recv), so a
/// responsive upstream that keeps completing ops resets its clock and is never
/// timed out; only a HANG (no completion within the budget) lets the deadline lapse.
fn set_proxy_deadline(d: &mut ProxyDial) {
    d.op_deadline = Instant::now() + proxy_timeout();
}

/// Take the in-flight proxy dial box for `slot` (if any), decrementing the shard's
/// `proxy_inflight` count so the wait loop stops sweeping once no dial remains. The
/// single chokepoint for clearing `conn.proxy`, keeping the count exact.
fn take_proxy(sh: &mut Shard, slot: u32) -> Option<Box<ProxyDial>> {
    let d = sh.slab.get(slot).and_then(|c| c.proxy.take());
    if d.is_some() {
        sh.proxy_inflight = sh.proxy_inflight.saturating_sub(1);
    }
    d
}

/// Fail every NATIVE proxy dial whose outstanding upstream op has blown its deadline
/// (a hung/slow upstream: a connect that never lands, or a recv that never delivers).
/// Collect the expired slots first (the fail path re-enters the slab), then:
///   * still connecting / buffering the head (`!stream`) ⇒ [`proxy_dial_failed`]: a
///     502 through the proven transform + the upstream fd recycled — the SAME path a
///     connect/recv ERROR takes.
///   * already streaming (`stream`, the head is on the wire) ⇒ [`close`]: the client
///     response has begun, so a 502 is impossible; truncate with a clean close and
///     recycle the upstream fd.
/// Cheap: returns immediately when no dial is outstanding, and only scans the slab on
/// a sweep tick (which only fires while `proxy_inflight > 0`).
fn sweep_proxy_timeouts(sh: &mut Shard) {
    if sh.proxy_inflight == 0 {
        return;
    }
    let now = Instant::now();
    let mut expired: Vec<u32> = Vec::new();
    for (i, slot) in sh.slab.conns.iter().enumerate() {
        if let Some(c) = slot {
            if let Some(d) = c.proxy.as_ref() {
                if now >= d.op_deadline {
                    expired.push(i as u32);
                }
            }
        }
    }
    for slot in expired {
        let streaming = sh
            .slab
            .get(slot)
            .and_then(|c| c.proxy.as_ref())
            .map(|d| d.stream)
            .unwrap_or(false);
        eprintln!(
            "dataplane: io_uring NATIVE proxyDial TIMEOUT (slot={slot}, streaming={streaming}) \
             — hung upstream past {}ms deadline; {} + recycle upstream fd",
            proxy_timeout().as_millis(),
            if streaming { "truncating close" } else { "502" }
        );
        if streaming {
            close(sh, slot);
        } else {
            proxy_dial_failed(sh, slot);
        }
    }
}

// --- NATIVE second-socket proxy dial (the `TAG_YIELD_PROXY` realization) --------

/// Fill a boxed `sockaddr_storage` from a `SocketAddr` for a connect SQE; returns
/// the address length. The boxed storage gives a stable address the in-flight
/// connect op can reference.
fn fill_sockaddr(addr: SocketAddr, ss: &mut libc::sockaddr_storage) -> libc::socklen_t {
    match addr {
        SocketAddr::V4(a) => {
            // SAFETY: writing the IPv4 view of a zeroed storage; `sockaddr_in` fits.
            let sin = ss as *mut _ as *mut libc::sockaddr_in;
            unsafe {
                (*sin).sin_family = libc::AF_INET as libc::sa_family_t;
                (*sin).sin_port = a.port().to_be();
                (*sin).sin_addr = libc::in_addr {
                    s_addr: u32::from_ne_bytes(a.ip().octets()),
                };
            }
            std::mem::size_of::<libc::sockaddr_in>() as libc::socklen_t
        }
        SocketAddr::V6(a) => {
            // SAFETY: writing the IPv6 view of a zeroed storage; `sockaddr_in6` fits.
            let sin6 = ss as *mut _ as *mut libc::sockaddr_in6;
            unsafe {
                (*sin6).sin6_family = libc::AF_INET6 as libc::sa_family_t;
                (*sin6).sin6_port = a.port().to_be();
                (*sin6).sin6_addr = libc::in6_addr {
                    s6_addr: a.ip().octets(),
                };
            }
            std::mem::size_of::<libc::sockaddr_in6>() as libc::socklen_t
        }
    }
}

/// Begin the NATIVE upstream dial for `slot`: resolve the proven-picked `backend`
/// to its configured address, open a shard-owned SECOND socket, and submit the
/// connect SQE. On any setup failure (no fleet/addr, socket create) the dial
/// short-circuits to a 502 threaded through resume — byte-identical to the blocking
/// interpreter's `bad_gateway()` on the same failure. `conn.step` stays parked (its
/// replay context is reused when the reply is threaded into `submit_resume`).
fn start_proxy_dial(sh: &mut Shard, slot: u32, backend: u32, forward_req: Vec<u8>) {
    let addr = match crate::proxy_hook::fleet().and_then(|f| f.addr(backend)) {
        Some(a) => a,
        // No fleet or the id maps to no socket: 502 through the proven transform,
        // exactly as `interp::run_effect_serve`'s `None => bad_gateway()` arm.
        None => return push_result_and_resume(sh, slot, crate::proxy_dial::bad_gateway()),
    };
    let domain = match addr {
        SocketAddr::V4(_) => libc::AF_INET,
        SocketAddr::V6(_) => libc::AF_INET6,
    };
    // SAFETY: socket(2) with a valid domain/type; the returned fd is checked and
    // owned by this ProxyDial until it is closed exactly once when the dial ends.
    let up_fd = unsafe { libc::socket(domain, libc::SOCK_STREAM | libc::SOCK_CLOEXEC, 0) };
    if up_fd < 0 {
        crate::proxy_hook::fleet().map(|f| f.record_failure(backend));
        return push_result_and_resume(sh, slot, crate::proxy_dial::bad_gateway());
    }
    eprintln!(
        "dataplane: io_uring NATIVE proxyDial(backend={backend} addr={addr}) — \
         second-socket SQE path (connect/send/recv on the shard, no blocking fallback)"
    );
    let mut storage: Box<libc::sockaddr_storage> = Box::new(unsafe { std::mem::zeroed() });
    let addr_len = fill_sockaddr(addr, &mut storage);
    let dial = Box::new(ProxyDial {
        up_fd,
        backend,
        forward_req,
        sent: 0,
        up_acc: Vec::with_capacity(RECV_CHUNK),
        addr: storage,
        framing: ReplyFraming::Unknown,
        head_end: None,
        chunk_parser: crate::proxy_dial::ChunkedParser::new(),
        chunk_fed: 0,
        stream: false,
        stream_target: 0,
        stream_forwarded: 0,
        // The connect op must land within one timeout budget or the sweep fails it.
        op_deadline: Instant::now() + proxy_timeout(),
    });
    let addr_ptr = dial.addr.as_ref() as *const libc::sockaddr_storage as *const libc::sockaddr;
    match sh.slab.get(slot) {
        Some(conn) => conn.proxy = Some(dial),
        None => {
            // Connection vanished before we could park the dial: close the fd.
            unsafe { libc::close(up_fd) };
            return;
        }
    }
    // A dial is now parked: the wait loop will sweep its deadline until it clears.
    sh.proxy_inflight += 1;
    let sqe = opcode::Connect::new(types::Fd(up_fd), addr_ptr, addr_len)
        .build()
        .user_data(TAG_PROXY_CONNECT | slot as u64);
    sh.backlog.push(sqe);
}

/// Connect completed: on success, send the forward request; on failure, 502 through
/// the proven transform (the breaker takes the failure).
fn on_proxy_connect(sh: &mut Shard, slot: u32, res: i32) {
    if res < 0 {
        return proxy_dial_failed(sh, slot);
    }
    // SAFETY: `forward_req` lives in the boxed ProxyDial in the slab; its heap
    // allocation is stable for the in-flight send op (untouched until completion).
    let sqe = match sh.slab.get(slot).and_then(|c| c.proxy.as_mut()) {
        Some(d) => {
            set_proxy_deadline(d); // the forward send now owns the deadline
            let ptr = d.forward_req.as_ptr();
            let len = d.forward_req.len() as u32;
            opcode::Send::new(types::Fd(d.up_fd), ptr, len)
                .build()
                .user_data(TAG_PROXY_SEND | slot as u64)
        }
        None => return,
    };
    sh.backlog.push(sqe);
}

/// Send completed: advance the sent offset; send the remainder on a short write,
/// else arm the first upstream recv. A send error is a 502.
fn on_proxy_send(sh: &mut Shard, slot: u32, res: i32) {
    if res <= 0 {
        return proxy_dial_failed(sh, slot);
    }
    let (up_fd, more) = match sh.slab.get(slot).and_then(|c| c.proxy.as_mut()) {
        Some(d) => {
            d.sent += res as usize;
            (d.up_fd, d.sent < d.forward_req.len())
        }
        None => return,
    };
    if more {
        // Short write: send the unsent tail.
        let sqe = match sh.slab.get(slot).and_then(|c| c.proxy.as_mut()) {
            Some(d) => {
                set_proxy_deadline(d); // the resend now owns the deadline
                // SAFETY: the tail lives in the boxed ProxyDial, stable across the op.
                let ptr = unsafe { d.forward_req.as_ptr().add(d.sent) };
                let len = (d.forward_req.len() - d.sent) as u32;
                opcode::Send::new(types::Fd(up_fd), ptr, len)
                    .build()
                    .user_data(TAG_PROXY_SEND | slot as u64)
            }
            None => return,
        };
        sh.backlog.push(sqe);
        return;
    }
    arm_proxy_recv(sh, slot);
}

/// Arm one upstream recv into the reserved tail of `up_acc`. Same reserve-then-fill
/// discipline as `recv_sqe`: reserve `RECV_CHUNK`, aim the SQE at the tail, and
/// extend the logical length on completion.
fn arm_proxy_recv(sh: &mut Shard, slot: u32) {
    let sqe = match sh.slab.get(slot).and_then(|c| c.proxy.as_mut()) {
        Some(d) => {
            set_proxy_deadline(d); // this recv now owns the deadline
            d.up_acc.reserve(RECV_CHUNK);
            let len = d.up_acc.len();
            // SAFETY: `reserve` guaranteed `RECV_CHUNK` bytes past `len`; the pointer
            // is valid for that many bytes and the kernel initializes them. Only one
            // recv is in flight per dial, so the tail is not aliased.
            let ptr = unsafe { d.up_acc.as_mut_ptr().add(len) };
            opcode::Recv::new(types::Fd(d.up_fd), ptr, RECV_CHUNK as u32)
                .build()
                .user_data(TAG_PROXY_RECV | slot as u64)
        }
        None => return,
    };
    sh.backlog.push(sqe);
}

/// Whether the NATIVE RSS-bounded passthrough streaming path is enabled for non-gzip
/// fixed-`Content-Length` proxy replies (the default). Set `DRORB_PROXY_NOSTREAM=1` to
/// force the buffered `drorb_serve_resume` path for EVERY reply — the A/B contrast the
/// RSS measurement uses (streaming = bounded, buffered = grows ~body). Read once.
fn native_proxy_stream_enabled() -> bool {
    use std::sync::OnceLock;
    static STREAM: OnceLock<bool> = OnceLock::new();
    *STREAM.get_or_init(|| {
        !std::env::var("DRORB_PROXY_NOSTREAM")
            .map(|v| matches!(v.as_str(), "1" | "true" | "yes" | "on"))
            .unwrap_or(false)
    })
}

/// Upstream recv completed: EOF ends a close-delimited reply; `res > 0` extends the
/// accumulator and either completes the reply (thread it into resume) or arms
/// another recv. A recv error is a 502.
fn on_proxy_recv(sh: &mut Shard, slot: u32, res: i32) {
    match res {
        0 => {
            // EOF: the upstream closed. While STREAMING a fixed-CL reply this is the end
            // of the body (or a truncation) — finish the stream and continue/close the
            // client. Otherwise (buffered path) it is the framed end of a close-delimited
            // reply — thread what we have into resume.
            let streaming = sh
                .slab
                .get(slot)
                .and_then(|c| c.proxy.as_ref())
                .map(|d| d.stream)
                .unwrap_or(false);
            if streaming {
                proxy_stream_finish(sh, slot);
            } else {
                proxy_reply_done(sh, slot);
            }
        }
        n if n > 0 => {
            // Extend the accumulator with the just-received bytes.
            let streaming = match sh.slab.get(slot).and_then(|c| c.proxy.as_mut()) {
                Some(d) => {
                    // SAFETY: the kernel wrote `n` bytes into the reserved tail (see
                    // `arm_proxy_recv`); extend the logical length to cover them.
                    let new_len = d.up_acc.len() + n as usize;
                    unsafe { d.up_acc.set_len(new_len) };
                    d.stream
                }
                None => return,
            };
            if streaming {
                // STREAMING: forward this body chunk straight to the client; `up_acc` is
                // drained after each forward, so the body is never held whole.
                proxy_stream_forward_chunk(sh, slot);
                return;
            }
            // Not yet streaming: decide the framing (sets head_end), then either start
            // passthrough streaming (non-gzip fixed-CL) or run the buffered path.
            let complete = match sh.slab.get(slot).and_then(|c| c.proxy.as_mut()) {
                Some(d) => d.reply_complete(),
                None => return,
            };
            if try_start_proxy_stream(sh, slot) {
                return; // awaiting the transformed head from the seam
            }
            if complete {
                proxy_reply_done(sh, slot);
            } else {
                arm_proxy_recv(sh, slot);
            }
        }
        _ => proxy_dial_failed(sh, slot), // recv error
    }
}

/// Once the upstream HEAD is complete and the framing is a fixed `Content-Length`, submit
/// the CL-trust streaming-head seam (`drorb_serve_proxy_stream_head`) with the ORIGINAL
/// request, the raw upstream head (through `\r\n\r\n`), and the declared body length. The
/// seam returns the transformed head (non-gzip) or EMPTY (gzip). Returns `true` when the
/// seam was submitted (the shard now awaits the head reply and arms no more recvs);
/// `false` when streaming does not apply (chunked / EOF framing, disabled, head not yet
/// complete, or the step/request state is gone) so the caller runs the buffered path.
fn try_start_proxy_stream(sh: &mut Shard, slot: u32) -> bool {
    if !native_proxy_stream_enabled() {
        return false;
    }
    // Extract (req, up_head bytes, body_len) if this reply is a fixed-CL, head-complete,
    // not-yet-streaming dial with a parked request.
    let framed: Option<(Vec<u8>, Vec<u8>, usize)> = {
        let conn = match sh.slab.get(slot) {
            Some(c) => c,
            None => return false,
        };
        let d = match conn.proxy.as_ref() {
            Some(d) if !d.stream => d,
            _ => return false,
        };
        let he = match d.head_end {
            Some(he) => he,
            None => return false,
        };
        let target = match d.framing {
            ReplyFraming::Fixed(t) => t,
            _ => return false, // only fixed Content-Length streams
        };
        let req = match conn.step.as_ref() {
            Some(st) => st.req.clone(),
            None => return false,
        };
        let up_head = d.up_acc[..he].to_vec();
        Some((req, up_head, target - he))
    };
    let (req, up_head, body_len) = match framed {
        Some(v) => v,
        None => return false,
    };
    let reply = ServeReply::Shard(sh.mtx.clone(), sh.efd, slot);
    if sh
        .gw
        .submit_proxy_stream_head(&req, &up_head, body_len, reply)
    {
        if let Some(conn) = sh.slab.get(slot) {
            conn.awaiting_stream_head = true;
        }
        true
    } else {
        false
    }
}

/// The transformed streaming head has come back from the seam. On a NON-EMPTY (non-gzip)
/// head: send `head ++ (any body bytes already received)` to the client and enter
/// passthrough streaming — the body forwards through, RSS-bounded, byte-identical to the
/// buffered `proxyRespTransform` (`Reactor.ServeStep.proxyStream_bytes_faithful`). On an
/// EMPTY head (the request accepts gzip — the head re-encodes): fall back to the buffered
/// `drorb_serve_resume` path (keep accumulating; stay open honestly on chunked TE).
fn on_stream_head_reply(sh: &mut Shard, slot: u32, head: PooledBuf) {
    if let Some(conn) = sh.slab.get(slot) {
        conn.awaiting_stream_head = false;
    }
    if head.is_empty() {
        // gzip reply: do NOT stream. Resume the buffered path over what we have.
        let complete = match sh.slab.get(slot).and_then(|c| c.proxy.as_mut()) {
            Some(d) => d.reply_complete(),
            None => return,
        };
        if complete {
            proxy_reply_done(sh, slot);
        } else {
            arm_proxy_recv(sh, slot);
        }
        return;
    }
    // Non-gzip: build the first client send = transformed head ++ the body bytes already
    // received (clamped to the declared Content-Length), then stream the rest through.
    let conn = match sh.slab.get(slot) {
        Some(c) => c,
        None => return,
    };
    let mut out = sh.gw.pool().take();
    out.clear();
    out.extend_from_slice(&head);
    // OBSERVABILITY: retain the transformed head so the whole streamed proxy response
    // can be recorded ONCE at `proxy_stream_finish` (status read from this head, byte
    // total = head + streamed body) — the streamed analogue of blocking's emit_streamed.
    conn.stream_head = Some(head.to_vec());
    // Annotate the `Connection:` disposition into the HEAD exactly as `stage_response`
    // does on the buffered path, so the streamed head is byte-identical to it (the head
    // carries Content-Length ⇒ self-delimited ⇒ keep-alive honours the request intent).
    let keepalive =
        conn.req_keepalive && !conn.h2c && crate::http::response_is_self_delimited(&out);
    if !conn.h2c {
        crate::http::annotate_connection(&mut out, keepalive);
    }
    let (he, target) = match conn.proxy.as_ref() {
        Some(d) => (
            d.head_end.unwrap_or(d.up_acc.len()),
            d.stream_target_from_framing(),
        ),
        None => return,
    };
    if let Some(d) = conn.proxy.as_mut() {
        d.stream = true;
        d.stream_target = target;
        let avail = d.up_acc.len().saturating_sub(he);
        let take = avail.min(target);
        out.extend_from_slice(&d.up_acc[he..he + take]);
        d.stream_forwarded = take;
        d.up_acc.clear();
    }
    conn.keepalive = keepalive;
    conn.resp = Some(out);
    conn.sent = 0;
    conn.zc_issued = 0;
    conn.zc_data = 0;
    conn.zc_notif_exp = 0;
    conn.zc_notif = 0;
    conn.zc_error = false;
    push_send(sh, slot);
}

/// Forward one just-received upstream body chunk to the client during streaming, clamped
/// to the remaining `Content-Length`, then drain `up_acc` so the body is never held whole.
fn proxy_stream_forward_chunk(sh: &mut Shard, slot: u32) {
    let conn = match sh.slab.get(slot) {
        Some(c) => c,
        None => return,
    };
    let mut out = sh.gw.pool().take();
    out.clear();
    if let Some(d) = conn.proxy.as_mut() {
        let remaining = d.stream_target.saturating_sub(d.stream_forwarded);
        let take = d.up_acc.len().min(remaining);
        out.extend_from_slice(&d.up_acc[..take]);
        d.stream_forwarded += take;
        d.up_acc.clear();
    } else {
        return;
    }
    conn.resp = Some(out);
    conn.sent = 0;
    conn.zc_issued = 0;
    conn.zc_data = 0;
    conn.zc_notif_exp = 0;
    conn.zc_notif = 0;
    conn.zc_error = false;
    push_send(sh, slot);
}

/// After a streamed client send completes: forward the next upstream chunk, or — once the
/// whole declared body has been forwarded — finish the stream. Returns `true` if it
/// handled the completion (the caller must NOT run the normal `finish_send`).
fn proxy_stream_after_send(sh: &mut Shard, slot: u32) -> bool {
    let done = match sh.slab.get(slot).and_then(|c| c.proxy.as_ref()) {
        Some(d) if d.stream => d.stream_forwarded >= d.stream_target,
        _ => return false,
    };
    if let Some(conn) = sh.slab.get(slot) {
        conn.resp = None;
        conn.sent = 0;
        conn.zc_issued = 0;
        conn.zc_data = 0;
        conn.zc_notif_exp = 0;
        conn.zc_notif = 0;
        conn.zc_error = false;
    }
    if done {
        proxy_stream_finish(sh, slot);
    } else {
        arm_proxy_recv(sh, slot);
    }
    true
}

/// The passthrough stream is complete: record the fleet success, close the upstream
/// socket, drop the proxy + parked step state, recycle any held receive lease, then
/// continue the client connection (keep-alive) or close it.
fn proxy_stream_finish(sh: &mut Shard, slot: u32) {
    let (backend, forwarded) = match take_proxy(sh, slot) {
        Some(d) => {
            // SAFETY: closing the shard-owned upstream fd exactly once, now the dial is
            // finished and no SQE references it.
            unsafe { libc::close(d.up_fd) };
            (Some(d.backend), d.stream_forwarded)
        }
        None => (None, 0),
    };
    if let Some(b) = backend {
        crate::proxy_hook::fleet().map(|f| f.record_success(b));
    }
    let bid = sh.slab.get(slot).and_then(|c| c.leased_bid.take());
    if let (Some(bid), Some(br)) = (bid, sh.br.as_mut()) {
        br.recycle(bid);
        ZC_RECYCLE.fetch_add(1, Ordering::Relaxed);
    }
    let keepalive = match sh.slab.get(slot) {
        Some(conn) => {
            conn.step = None;
            // OBSERVABILITY: one record for the whole streamed passthrough response
            // (mirrors blocking's post-stream emit_streamed): status from the retained
            // head, byte total = head + streamed body. `backend = None` — the effect-seam
            // path records None, as blocking does; the fleet already bumped the backend.
            if let Some(head) = conn.stream_head.take() {
                let total = head.len() as u64 + forwarded as u64;
                crate::metrics::record_streamed(&head, total, None);
                if let Some((rl, client)) = &conn.logrec {
                    crate::access_log::log_streamed(
                        *client,
                        rl,
                        &head,
                        total,
                        None,
                        conn.req_start,
                    );
                }
            }
            conn.keepalive
        }
        None => return,
    };
    finish_send(sh, slot, keepalive);
}

/// The upstream reply is complete: close the second socket, record the fleet
/// success, and thread the accumulated reply bytes into `submit_resume`. The proven
/// core replays `serveStep` with this one recorded result and computes
/// `proxyRespTransform input upstream` — the same bytes the blocking oracle produces
/// — returning the DONE response, which the next `on_step_reply` stages and sends.
fn proxy_reply_done(sh: &mut Shard, slot: u32) {
    let (upstream, backend) = match take_proxy(sh, slot) {
        Some(d) => {
            // SAFETY: closing the shard-owned upstream fd exactly once, now the dial
            // is finished and no SQE references it.
            unsafe { libc::close(d.up_fd) };
            (d.up_acc, d.backend)
        }
        None => return,
    };
    crate::proxy_hook::fleet().map(|f| f.record_success(backend));
    eprintln!(
        "dataplane: io_uring NATIVE proxyDial(backend={backend}) upstream reply complete \
         ({} bytes) — threading into drorb_serve_resume (proxyRespTransform)",
        upstream.len()
    );
    push_result_and_resume(sh, slot, upstream);
}

/// The dial failed (connect/send/recv error, or no reachable address): close any
/// second socket, record the fleet failure (opening the breaker after the
/// threshold), and thread a `502 Bad Gateway` through the proven transform — the
/// SAME bytes `interp::run_effect_serve` threads on a dial failure.
fn proxy_dial_failed(sh: &mut Shard, slot: u32) {
    let backend = match take_proxy(sh, slot) {
        Some(d) => {
            // SAFETY: closing the shard-owned upstream fd exactly once.
            unsafe { libc::close(d.up_fd) };
            Some(d.backend)
        }
        None => None,
    };
    if let Some(b) = backend {
        crate::proxy_hook::fleet().map(|f| f.record_failure(b));
    }
    push_result_and_resume(sh, slot, crate::proxy_dial::bad_gateway());
}

/// Append one recorded effect `result` to `slot`'s replay list and `submit_resume`
/// the proven core — the async analogue of `interp::run_effect_serve`'s
/// `results.push(...)` + loop `call_seam`. Delivers the next `Step` back to this
/// shard's mailbox (keyed by `slot`), decoded by the next `on_step_reply`.
fn push_result_and_resume(sh: &mut Shard, slot: u32, result: Vec<u8>) {
    let reply = ServeReply::Shard(sh.mtx.clone(), sh.efd, slot);
    let ok = match sh.slab.get(slot) {
        Some(conn) => match conn.step.as_mut() {
            Some(st) => {
                st.results.push(result);
                sh.gw.submit_resume(
                    st.prefix,
                    st.mask,
                    &st.req,
                    &st.results,
                    st.resume_seam,
                    reply,
                )
            }
            None => return,
        },
        None => return,
    };
    if !ok {
        // Serve thread gone (shutdown): drop the effect state and close.
        if let Some(conn) = sh.slab.get(slot) {
            conn.step = None;
        }
        close(sh, slot);
    }
}

/// DEFER one effect-seam request off the shard: hand its ORIGINAL request bytes to a
/// blocking fallback thread that runs the full `interp::run_effect_serve` (the
/// proven blocking interpreter — the correctness oracle) and posts the final
/// response back to this shard's mailbox. The blocking wait (a coalescing condvar,
/// a disk read, a proxy dial) happens ON THAT THREAD, never on the shard. This is
/// the honest Phase-0 fallback for the effects Phase 1/2 will lower onto the SQE
/// path (cold-key WAITER, DRORB_DISK_CACHE, proxyDial); it does not fake them.
fn defer_to_blocking(sh: &mut Shard, slot: u32) {
    // Take the parked step state; the reply comes back as a FINAL response (the
    // connection is no longer awaiting a `Step`), staged by the normal path.
    let st = match sh.slab.get(slot).and_then(|c| c.step.take()) {
        Some(st) => st,
        None => return,
    };
    if let Some(conn) = sh.slab.get(slot) {
        conn.req_keepalive = st.keepalive;
    }
    let gw = sh.gw.clone();
    let mtx = sh.mtx.clone();
    let efd = sh.efd;
    let req = st.req;
    let spawned = std::thread::Builder::new()
        .name(format!("drorb-defer-{slot}"))
        .spawn(move || {
            // A private reply channel to the (single, shared) serve thread — the
            // blocking interpreter's own step/resume/effect crossings ride it. The
            // BLOCK is on this fallback thread, not the shard.
            let (reply_tx, reply_rx) = channel::<PooledBuf>();
            let bytes = crate::interp::run_effect_serve(&req, &gw, &reply_tx, &reply_rx)
                .unwrap_or_else(|| {
                    // The seam declined (e.g. proxy yield with no fleet): fall back to
                    // a plain metered serve so the request still gets a response.
                    let meter = Meter {
                        client: "0.0.0.0".parse().unwrap(),
                        seq: 0,
                    };
                    gw.call_metered_cfg(&[], &req, meter, &reply_tx, &reply_rx)
                        .map(|b| b.to_vec())
                        .unwrap_or_default()
                });
            let mut resp = gw.pool().take();
            resp.extend_from_slice(&bytes);
            if mtx
                .send(ShardDone {
                    conn: slot,
                    resp,
                    split_static: false,
                })
                .is_ok()
            {
                wake(efd);
            }
        });
    if spawned.is_err() {
        // Could not spawn the fallback thread: close the connection rather than hang.
        close(sh, slot);
    }
}

/// Plain (pooled) recv completion: the kernel wrote `res` bytes into the acc tail.
fn on_recv(sh: &mut Shard, slot: u32, res: i32) {
    let n = match res {
        n if n > 0 => n as usize,
        _ => return close(sh, slot), // 0 = EOF, <0 = error
    };
    {
        let conn = match sh.slab.get(slot) {
            Some(c) => c,
            None => return,
        };
        // SAFETY: the kernel wrote `n` bytes into the reserved tail region of
        // `acc` (see `recv_sqe`); extending the logical length to cover the
        // now-initialized bytes is sound.
        let new_len = conn.acc.len() + n;
        unsafe { conn.acc.set_len(new_len) };
    }
    dispatch_acc(sh, slot);
}

/// Buffer-select recv completion: the kernel lent buffer `bid` (in `flags`) and
/// wrote `res` bytes into it. This is the model's `deliver` edge.
fn on_recv_br(sh: &mut Shard, slot: u32, res: i32, flags: u32) {
    // Exhaustion: no free provided buffer was available (the model's `exhaust`).
    // Fall back to a plain pooled recv into the acc buffer so the connection makes
    // progress; the ring self-heals as leases recycle.
    if res == -libc::ENOBUFS {
        let sqe = match sh.slab.get(slot) {
            Some(conn) => recv_sqe(conn, slot),
            None => return,
        };
        sh.backlog.push(sqe);
        return;
    }
    let n = match res {
        n if n > 0 => n as usize,
        _ => return close(sh, slot), // 0 = EOF, <0 = error
    };
    let bid = match cqueue::buffer_select(flags) {
        Some(b) => b,
        None => return close(sh, slot), // success without a buffer id: cannot locate data
    };

    // Is the accumulation buffer empty (a fresh request starts in this slot)?
    let acc_empty = match sh.slab.get(slot) {
        Some(c) => c.acc.is_empty(),
        None => return recycle_bid(sh, bid), // conn gone: return the lease
    };

    // Borrow fast path only when this slot holds a whole HTTP/1.1 request with
    // nothing before or after it and it is not an h2c opener.
    let borrow = if acc_empty {
        // SAFETY: `bid` was just delivered and not yet recycled; `n <= RECV_CHUNK`.
        let slice = unsafe { sh.br.as_ref().unwrap().slice(bid, n) };
        let is_h2c = slice.starts_with(H2_PREFACE) || H2_PREFACE.starts_with(slice);
        matches!((is_h2c, next_request(slice)), (false, Frame::Complete(total)) if total == n)
    } else {
        false
    };

    if borrow {
        // The connection context the metered gates read: the client address (accept
        // peer, or the forwarded client when the peer is a trusted proxy) and the
        // per-connection request index. Read `peer_ip`/`conn_seq` before the slice.
        let (peer_ip, seq) = match sh.slab.get(slot) {
            Some(c) => (c.peer_ip, c.conn_seq),
            None => return recycle_bid(sh, bid),
        };
        // Which metered fold this connection serves — the SAME choice
        // `blocking::handle_conn` makes: the braided deployment when braid-marked,
        // else the config-driven metered fold. `has_cfg` decides whether the cfg
        // seam's `cfgLen :: config :: request` frame is needed.
        let braid = crate::config::braid_enabled();
        let cfg = crate::config::get();
        // The RAW config bytes (policy directives + route table) drive the config seam
        // even when the ROUTE parser rejected the file (a policy-only config): a
        // non-empty raw config routes this connection through the cfg metered seam so
        // `Reactor.Deploy.parsePolicy` enforces the middleware policy. Empty ⇒ the
        // zero-copy `drorb_serve_metered` default (byte-identical).
        let raw = crate::config::raw_text();
        let has_cfg = cfg
            .as_ref()
            .map(|d| !d.config_text.is_empty())
            .unwrap_or(false)
            || !raw.is_empty();
        let (ptr, len, keepalive, meter, obs) = {
            // SAFETY: as above; the slice covers the whole request (`n`).
            let slice = unsafe { sh.br.as_ref().unwrap().slice(bid, n) };
            let client = crate::blocking::client_addr(slice, peer_ip);
            let meter = Meter { client, seq };
            // OBSERVABILITY capture on the zero-copy borrow path, from the leased slot
            // view (mirrors `blocking::handle_conn`): request line + effective client,
            // parsed only when the access log is enabled.
            let obs = if crate::access_log::enabled() {
                Some((crate::access_log::ReqLine::parse(slice), client))
            } else {
                None
            };
            (
                slice.as_ptr(),
                slice.len(),
                request_wants_keepalive(slice),
                meter,
                obs,
            )
        };
        match sh.slab.get(slot) {
            Some(conn) => {
                conn.req_keepalive = keepalive;
                conn.conn_seq = conn.conn_seq.wrapping_add(1);
                conn.req_start = Instant::now();
                conn.logrec = obs;
                // Header phase complete (a whole request arrived in one recv): the
                // slowloris gate no longer applies to this connection.
                conn.headers_done = true;
            }
            None => return recycle_bid(sh, bid),
        }
        let reply = ServeReply::Shard(sh.mtx.clone(), sh.efd, slot);

        // ZERO-COPY metered case: both the braided seam (`drorb_serve_metered_braided`)
        // and the DIRECT metered seam (`drorb_serve_metered`, used for a no/empty-config
        // deployment — byte-identical to the empty-config metered cfg fold) take the RAW
        // request, so the borrowed leased-slot view crosses with NO owned copy (copy #1
        // stays removed). The lease is held until the response returns.
        if braid || !has_cfg {
            ZC_BORROW.fetch_add(1, Ordering::Relaxed);
            match sh.slab.get(slot) {
                Some(conn) => {
                    conn.leased_bid = Some(bid);
                    // ZERO-COPY BODY (`DRORB_SPAN=15`): remember the borrowed request
                    // length so the split-response send can slice the echo body straight
                    // from this held lease slot (`br.slice(bid, req_len)`) — no copy.
                    conn.req_len = len;
                }
                None => return recycle_bid(sh, bid),
            }
            // SAFETY: the borrowed view stays valid until we recycle `bid`, which
            // happens only after this request's response returns — long after the
            // serve thread has read the bytes.
            let borrowed = unsafe { BorrowedReq::new(ptr, len) };
            let ok = if braid {
                sh.gw
                    .submit_borrowed_metered_braided(borrowed, meter, reply)
            } else {
                sh.gw.submit_borrowed_metered(borrowed, meter, reply)
            };
            if !ok {
                // Serve thread gone (shutdown): recycle this lease's slot exactly
                // once (keeping the borrow==recycle invariant) and close.
                if let Some(conn) = sh.slab.get(slot) {
                    conn.leased_bid = None;
                }
                recycle_bid(sh, bid);
                if sh.br.is_some() {
                    ZC_RECYCLE.fetch_add(1, Ordering::Relaxed);
                }
                close(sh, slot);
            }
            return;
        }

        // ABI FRICTION — copy #1 retained for the non-empty-config metered path: the
        // cfg metered seam consumes a `cfgLen(4 BE) :: config :: request` frame, and
        // the 4-byte length + config bytes cannot be prepended inside the leased
        // kernel slot. So this case copies the request out (into the framed buffer
        // the metered cfg submit builds), recycles the lease immediately, and submits
        // the framed metered cfg serve. Only a deployment with a non-empty
        // `DRORB_CONFIG` takes this path; the default / braided fast paths above stay
        // zero-copy.
        ZC_FALLBACK.fetch_add(1, Ordering::Relaxed);
        let cfg_bytes: &[u8] = match cfg.as_ref() {
            Some(d) => d.config_text.as_slice(),
            None => &raw,
        };
        // SAFETY: `bid`/`n` name the just-delivered slot, still leased here; the
        // metered cfg submit frames these bytes into its own pooled buffer before we
        // recycle the slot below.
        let slice = unsafe { sh.br.as_ref().unwrap().slice(bid, n) };
        let ok = sh
            .gw
            .submit_metered_cfg_bytes(cfg_bytes, slice, meter, reply);
        recycle_bid(sh, bid);
        if sh.br.is_some() {
            ZC_RECYCLE.fetch_add(1, Ordering::Relaxed);
        }
        if !ok {
            close(sh, slot);
        }
        return;
    }

    // Fallback: copy the slot bytes into acc (copy #1 retained for this
    // partial/pipelined/h2c case), recycle the lease immediately, then run the
    // normal accumulation-buffer framing.
    ZC_FALLBACK.fetch_add(1, Ordering::Relaxed);
    match sh.slab.get(slot) {
        Some(conn) => {
            // SAFETY: `bid`/`n` name the just-delivered slot; copy before recycle.
            let slice = unsafe { sh.br.as_ref().unwrap().slice(bid, n) };
            conn.acc.extend_from_slice(slice);
        }
        None => return recycle_bid(sh, bid),
    }
    recycle_bid(sh, bid);
    dispatch_acc(sh, slot);
}

/// Return a buffer id to the provided-buffer ring (no-op if not in zero-copy
/// mode). One recycle per lease — the running `Uring.recycle_at_most_once`.
fn recycle_bid(sh: &mut Shard, bid: u16) {
    if let Some(br) = sh.br.as_mut() {
        br.recycle(bid);
    }
}

/// Frame the accumulation buffer for `slot` and dispatch one complete request, or
/// arm another receive if more bytes are needed. Used by the plain path and by the
/// buf_ring fallback / keep-alive continuation.
fn dispatch_acc(sh: &mut Shard, slot: u32) {
    // SLOWLORIS gate — checked on EACH recv-driven re-entry, BEFORE framing. If this
    // connection's header phase (since accept) has overrun `slowloris-timeout` and its
    // first request has not yet been dispatched, drop it with the REAL proven `408`
    // (`slowloris_fires`, `Reactor/StandingCounters.lean`). Checking before framing is
    // what makes a slow DRIP that finally completes its head past the deadline still
    // refused — the classic slowloris drop, not a late serve. No recv op is
    // outstanding at this point (we are in the recv-completion handler), so the
    // teardown is race-free. `headers_done` connections and a `0` timeout never fire.
    let timeout = crate::config::slowloris_timeout();
    if !timeout.is_zero() {
        let expired = match sh.slab.get(slot) {
            Some(c) => {
                !c.headers_done
                    && crate::standing::header_expired(timeout, c.hdr_start, Instant::now())
            }
            None => return,
        };
        if expired {
            TIMEDOUT_408.fetch_add(1, Ordering::Relaxed);
            let mut resp = sh.gw.pool().take();
            resp.extend_from_slice(SLOWLORIS_408);
            stage_response(sh, slot, resp, false);
            return;
        }
    }
    let conn = match sh.slab.get(slot) {
        Some(c) => c,
        None => return,
    };

    // h2c preface: not HTTP/1.1-framed. Wait for the full preface, then hand the
    // connection to the interactive engine host on its own thread (the same fork
    // the blocking host makes).
    if !conn.h2c && conn.acc.len() < H2_PREFACE.len() && H2_PREFACE.starts_with(&conn.acc) {
        arm_recv(sh, slot);
        return;
    }
    if !conn.h2c && conn.acc.starts_with(H2_PREFACE) {
        return h2c_handoff(sh, slot);
    }

    match next_request(&conn.acc) {
        Frame::Complete(total) => {
            // MIXED-PORT OPENER CLASSIFICATION — the same rule as
            // `blocking::handle_conn`: a FIRST flight whose request line has no
            // `HTTP/` version token is neither protocol's well-formed opener — not
            // an HTTP/1.x request, and not the H2 preface (that forked to the
            // engine at the peek above). Terminate without a reply, the one answer
            // both protocols assign (RFC 9113 §3.4 invalid-preface connection
            // error — an HTTP/1.1 status line is only frame garbage to an H2
            // client; RFC 9112 §2.2/§3 close on a malformed request-line).
            if !conn.headers_done && crate::http::opener_lacks_http_version(&conn.acc[..total]) {
                return close(sh, slot);
            }
            let conn = match sh.slab.get(slot) {
                Some(c) => c,
                None => return,
            };
            let mut req = sh.gw.pool().take();
            req.extend_from_slice(&conn.acc[..total]);
            conn.acc.drain(..total);
            conn.req_keepalive = request_wants_keepalive(&req);
            // Header phase complete: the slowloris gate no longer applies to this
            // connection (the first request head has fully arrived and is dispatched).
            conn.headers_done = true;

            // OBSERVABILITY capture (mirrors `blocking::handle_conn` right before the
            // serve call): the effective client (accept peer, or the forwarded client
            // when the peer is a trusted proxy) + the request line + the start instant,
            // threaded to the response-sent point (`stage_response` / `proxy_stream_finish`)
            // where the metric and access-log line are emitted. The request line is
            // parsed only when the log is enabled.
            let obs_client = crate::blocking::client_addr(&req, conn.peer_ip);
            conn.req_start = Instant::now();
            conn.logrec = if crate::access_log::enabled() {
                Some((crate::access_log::ReqLine::parse(&req), obs_client))
            } else {
                None
            };

            // PHASE 0 effect seam (`DRORB_EFFECT_SEAM=1`): a proxy-route or
            // cacheable-shape request is driven through the proven `ServeStep`
            // effect program on the ASYNC io_uring path — submit the STEP
            // (non-blocking), park the continuation in `conn.step`, and drive the
            // resumes from `on_wakeup`/`on_step_reply`. `should_handle` is the SAME
            // host prefilter `blocking::handle_conn` uses; the proven core still owns
            // the real proxy/cache decision. The shard never blocks: the in-memory
            // cache effects resume inline and the blocking effects (disk / proxy /
            // coalescing waiter) defer to a fallback thread.
            if crate::interp::enabled() && crate::interp::should_handle(&req) {
                let keepalive = request_wants_keepalive(&req);
                let (step_seam, resume_seam, prefix) = crate::interp::seams();
                let mask = crate::interp::current_mask();
                let req_owned = req.to_vec();
                let reply = ServeReply::Shard(sh.mtx.clone(), sh.efd, slot);
                if sh.gw.submit_step(prefix, mask, &req, step_seam, reply) {
                    if let Some(c) = sh.slab.get(slot) {
                        c.step = Some(Box::new(StepState {
                            prefix,
                            mask,
                            req: req_owned,
                            results: Vec::new(),
                            resume_seam,
                            keepalive,
                        }));
                    }
                } else {
                    close(sh, slot);
                }
                return;
            }

            // Cross the METERED seam — the same dispatch `blocking::handle_conn`
            // runs: the connection's client address (accept peer, or the forwarded
            // client when the peer is a trusted proxy) and per-connection request
            // index are in scope, so the proven IP-filter and rate gates fire. The
            // default (no braid, no/empty config) is the config-driven metered fold
            // over the empty config = `servePipelineOfMetered defaultDeployment`,
            // byte-identical to the old plain `drorb_serve` where no gate fires
            // (`servePipelineOfMetered_default`). This is the correctness fix: the
            // metered/config/braid serve now runs on the default Linux fast path.
            let meter = Meter {
                client: crate::blocking::client_addr(&req, conn.peer_ip),
                seq: conn.conn_seq,
            };
            conn.conn_seq = conn.conn_seq.wrapping_add(1);
            let reply = ServeReply::Shard(sh.mtx.clone(), sh.efd, slot);
            let ok = if crate::config::braid_enabled() {
                sh.gw.submit_metered_braided_bytes(&req, meter, reply)
            } else {
                let cfg = crate::config::get();
                let raw = crate::config::raw_text();
                let cfg_bytes: &[u8] = match cfg.as_ref() {
                    Some(d) => d.config_text.as_slice(),
                    None => &raw,
                };
                sh.gw
                    .submit_metered_cfg_bytes(cfg_bytes, &req, meter, reply)
            };
            // `req` (owned pooled buffer) drops here: the metered submit copied /
            // framed its bytes into its own buffer, so it returns to the pool.
            if !ok {
                close(sh, slot);
            }
        }
        // Still incomplete — wait for more bytes. The slow-header deadline was already
        // consulted at the top of `dispatch_acc` (before framing), so a drip that
        // overruns the timeout is dropped there rather than looping here forever.
        Frame::NeedMore => arm_recv(sh, slot),
        Frame::Oversize => close(sh, slot),
    }
}

fn on_send(sh: &mut Shard, slot: u32, res: i32, flags: u32) {
    // ZERO-COPY BODY (`DRORB_SPAN=15`): a split `writev` completion (head + borrowed
    // body) — routed here by TAG_SEND, distinguished by an in-flight `split` state.
    if sh
        .slab
        .get(slot)
        .map(|c| c.split.is_some())
        .unwrap_or(false)
    {
        return on_split_send(sh, slot, res);
    }
    if sh.zc {
        return on_send_zc(sh, slot, res, flags);
    }
    // Baseline copying send: one completion per op.
    if res <= 0 {
        return close(sh, slot);
    }
    let whole_written = {
        let conn = match sh.slab.get(slot) {
            Some(c) => c,
            None => return,
        };
        conn.sent += res as usize;
        let total = conn.resp.as_ref().map(|r| r.len()).unwrap_or(0);
        if conn.sent < total {
            // Short write: send the remainder.
            let sqe = send_sqe(conn, slot, false);
            sh.backlog.push(sqe);
            return;
        }
        true
    };
    if !whole_written {
        return;
    }
    // Whole response written. If this was a streamed proxy chunk, continue the stream
    // (forward the next upstream chunk or finish) instead of the normal send tail.
    if sh
        .slab
        .get(slot)
        .and_then(|c| c.proxy.as_ref())
        .map(|d| d.stream)
        .unwrap_or(false)
    {
        proxy_stream_after_send(sh, slot);
        return;
    }
    // Not streaming: release the response (returns to the pool) and continue/close.
    let finished = match sh.slab.get(slot) {
        Some(conn) => {
            conn.resp = None;
            conn.sent = 0;
            conn.keepalive
        }
        None => return,
    };
    finish_send(sh, slot, finished);
}

/// Zero-copy send completion handling. Each `SendZc` posts a data completion
/// (`res` bytes sent); when it set `F_MORE` a later `F_NOTIF` completion marks its
/// send buffer free. We hold the response buffer until every issued op's data
/// completion is in *and* every expected notification has arrived — only then is
/// the buffer safe to release (return to the pool) and the slot safe to reuse.
fn on_send_zc(sh: &mut Shard, slot: u32, res: i32, flags: u32) {
    let settled = {
        let conn = match sh.slab.get(slot) {
            Some(c) => c,
            None => return,
        };
        if cqueue::notif(flags) {
            // A send buffer has been released by the kernel.
            ZC_NOTIF.fetch_add(1, Ordering::Relaxed);
            conn.zc_notif += 1;
        } else {
            // A data completion.
            conn.zc_data += 1;
            if cqueue::more(flags) {
                conn.zc_notif_exp += 1; // a notification will follow for this op
            }
            if res < 0 {
                conn.zc_error = true;
            } else {
                conn.sent += res as usize;
                let total = conn.resp.as_ref().map(|r| r.len()).unwrap_or(0);
                if !conn.zc_error && conn.sent < total {
                    // Short write: send the remainder as another zero-copy op.
                    let sqe = send_sqe(conn, slot, true);
                    conn.zc_issued += 1;
                    sh.backlog.push(sqe);
                }
            }
        }
        // The send sequence is fully settled once every issued op's data is in and
        // every promised notification has arrived. Only then may we free the
        // buffer / reuse the slot.
        conn.zc_data == conn.zc_issued && conn.zc_notif == conn.zc_notif_exp
    };
    if settled {
        finalize_zc_send(sh, slot);
    }
}

/// Finalize a settled zero-copy send: release the response buffer (returns to the
/// pool), then continue the connection (keep-alive) or close it.
fn finalize_zc_send(sh: &mut Shard, slot: u32) {
    // A settled streamed proxy chunk continues the stream (forward the next upstream
    // chunk or finish) rather than the normal keep-alive/close tail.
    if sh
        .slab
        .get(slot)
        .and_then(|c| c.proxy.as_ref())
        .map(|d| d.stream)
        .unwrap_or(false)
    {
        proxy_stream_after_send(sh, slot);
        return;
    }
    let keepalive = {
        let conn = match sh.slab.get(slot) {
            Some(c) => c,
            None => return,
        };
        let total = conn.resp.as_ref().map(|r| r.len()).unwrap_or(0);
        let ok = !conn.zc_error && conn.sent >= total;
        // `resp` drops here: the pooled response buffer returns to the pool.
        conn.resp = None;
        conn.sent = 0;
        conn.zc_issued = 0;
        conn.zc_data = 0;
        conn.zc_notif_exp = 0;
        conn.zc_notif = 0;
        conn.zc_error = false;
        ok && conn.keepalive
    };
    finish_send(sh, slot, keepalive);
}

/// Common tail of a completed send: continue the connection or close it.
fn finish_send(sh: &mut Shard, slot: u32, keepalive: bool) {
    if keepalive {
        dispatch_acc(sh, slot);
    } else {
        close(sh, slot);
    }
}

/// Fork an h2c prior-knowledge connection out of the shard to the interactive
/// engine host (`h2::host_conn`): ONE verified engine state threaded across
/// socket reads on a dedicated thread. SETTINGS synchronization, PING liveness
/// probes, and WINDOW_UPDATE-paced response bodies all arrive AFTER the
/// client's first flight (RFC 9113 §6.5.3/§6.7/§6.9), so the connection cannot
/// be answered by one shard-loop crossing — it leaves the shard for good, the
/// same fork the blocking host makes at its preface peek.
///
/// Mirrors `close`'s bookkeeping except the fd itself, whose ownership moves to
/// the host thread: any leased receive buffer recycles, any in-flight upstream
/// dial fd closes, the per-source standing counter decrements (the connection
/// leaves this shard's accounting at handoff, not at connection end), and the
/// slab entry drops with NO close SQE.
fn h2c_handoff(sh: &mut Shard, slot: u32) {
    let (fd, ip, burst) = match sh.slab.get(slot) {
        Some(conn) => {
            let mut burst = Vec::with_capacity(conn.acc.len());
            burst.extend_from_slice(&conn.acc);
            (conn.fd, conn.peer_ip, burst)
        }
        None => return,
    };
    let bid = sh.slab.get(slot).and_then(|c| c.leased_bid.take());
    if let (Some(bid), Some(br)) = (bid, sh.br.as_mut()) {
        br.recycle(bid);
        ZC_RECYCLE.fetch_add(1, Ordering::Relaxed);
    }
    if let Some(dial) = take_proxy(sh, slot) {
        // SAFETY: closing the shard-owned upstream fd exactly once (as `close`).
        unsafe { libc::close(dial.up_fd) };
    }
    sh.standing.on_close(ip);
    sh.slab.remove(slot); // drops the Conn: acc/resp buffers return to the pool
    // SAFETY: the slab entry is gone and no SQE references `fd` (the handoff
    // runs inside a recv-completion handler with no other op armed for this
    // slot), so the new TcpStream is the fd's sole owner; it moves to the host
    // thread and closes there.
    let stream = unsafe { std::net::TcpStream::from_raw_fd(fd) };
    let _ = stream.set_nonblocking(false); // host reads block under its timeouts
    std::thread::spawn(move || crate::h2::host_conn(stream, &burst));
}

fn close(sh: &mut Shard, slot: u32) {
    // Recycle any leased receive buffer before dropping the connection so no
    // buffer id is lost from the ring (recycle-exactly-once holds on this edge
    // too: the lease is recycled here iff it was not already recycled on a
    // response return).
    let bid = sh.slab.get(slot).and_then(|c| c.leased_bid.take());
    if let (Some(bid), Some(br)) = (bid, sh.br.as_mut()) {
        br.recycle(bid);
        ZC_RECYCLE.fetch_add(1, Ordering::Relaxed);
    }
    // Close any in-flight NATIVE proxy second socket before dropping the connection,
    // so the upstream fd is never leaked when a client connection is torn down
    // mid-dial (the copy-once/recycle discipline for the upstream fd).
    if let Some(dial) = take_proxy(sh, slot) {
        // SAFETY: closing the shard-owned upstream fd exactly once. Any in-flight
        // upstream SQE completes with an error afterward and its handler no-ops
        // (the ProxyDial is gone).
        unsafe { libc::close(dial.up_fd) };
    }
    if let Some(conn) = sh.slab.get(slot) {
        let fd = conn.fd;
        let ip = conn.peer_ip;
        sh.backlog.push(close_sqe(fd));
        // Decrement the per-source standing counter EXACTLY ONCE — this is the
        // single close funnel every connection (served, refused, EOF, error, proxy
        // teardown) exits through, so the increment at accept is matched here on
        // every path (conn_conservation; no leak that would wedge the gate).
        sh.standing.on_close(ip);
    }
    sh.slab.remove(slot); // drops the Conn: acc/resp buffers return to the pool
}

// --- submission plumbing --------------------------------------------------

/// Move every backlogged SQE into the submission queue, submitting to the kernel
/// to free slots whenever the queue fills.
fn flush(ring: &mut IoUring, backlog: &mut Vec<squeue::Entry>) -> std::io::Result<()> {
    while !backlog.is_empty() {
        let mut pushed = 0;
        {
            let mut sq = ring.submission();
            for e in backlog.iter() {
                // SAFETY: each `e` describes a valid op whose referenced buffers
                // (recv tail of `acc`, provided-ring slot, `resp` bytes, `efd_buf`)
                // outlive the op — they live in the slab / ring / loop until the
                // matching completion.
                if unsafe { sq.push(e) }.is_err() {
                    break; // SQ full
                }
                pushed += 1;
            }
        }
        backlog.drain(..pushed);
        if pushed == 0 {
            // SQ full and nothing drained: submit to free slots, then retry.
            ring.submit()?;
        }
    }
    Ok(())
}
