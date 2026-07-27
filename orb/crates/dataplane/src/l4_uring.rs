//! The single-threaded io_uring realisation of the layer-4 (raw TCP) passthrough
//! splice pump — the same proven `L4.Splice` forwarding model the blocking host
//! shell in [`crate::l4`] realises, but driven by one completion ring per shard
//! instead of two blocking `splice(2)` threads per connection.
//!
//! ## What this replaces
//!
//! The portable shell moves each connection's two directions on two OS threads,
//! each parked inside a blocking `splice(2)`. That is correct (it is the host of
//! `L4.Splice`), but it costs two threads for every live flow. This module drives
//! ALL flows on ONE thread: every fill and every drain is an `IORING_OP_SPLICE`
//! submission, and the kernel posts a completion when it is done. A thousand idle
//! passthrough flows cost one parked `io_uring_enter`, not two thousand threads.
//!
//! ## The proven model it realises, unchanged
//!
//! `L4.Splice.deployed_splice_faithful` proves one direction byte-transparent
//! under the DEPLOYED schedule `drainLoop chunk fuel` — the chunked LOCKSTEP loop
//!
//! ```text
//!   pull chunk ; push chunk ; pull chunk ; push chunk ; …
//! ```
//!
//! fill the pipe with at most `chunk` (= `SPLICE_CHUNK`, 64 KiB) bytes from the
//! source, drain EXACTLY those to the destination, repeat until the source is at
//! EOF and the pipe is empty. `deployed_relay_faithful` lifts that to both
//! directions independently (`projUp` / `projDown`). This module issues that
//! exact schedule: each direction is a `Phase::Fill` (source socket → pipe) whose
//! completion arms a `Phase::Drain` (pipe → destination socket) of exactly the
//! filled byte count, whose completion re-arms the next fill. One SQE per phase,
//! one phase in flight per direction at a time — the lockstep the proof pins.
//! Byte-transparency is therefore the proven `deployed_splice_faithful`, not an
//! asserted property of this code: this file only chooses WHEN each already-proven
//! fill/drain step is submitted, never WHAT bytes move.
//!
//! Half-close is honoured exactly as the blocking shell honours it: a source EOF
//! (a fill completing with 0) shuts down the write half of that direction's
//! destination, so the peer sees the close, while the opposite direction keeps
//! draining until it too reaches EOF. The flow's sockets and pipes are closed
//! only once BOTH directions have finished — so no completion can ever reference
//! a freed fd.

use std::net::{Shutdown, SocketAddr, TcpListener, TcpStream};
use std::os::fd::{AsRawFd, FromRawFd, RawFd};
use std::sync::Arc;
use std::sync::atomic::Ordering;
use std::sync::mpsc::{Receiver, Sender};
use std::time::Duration;

use io_uring::{IoUring, opcode, squeue, types};

use crate::pool::PooledBuf;
use crate::proxy_dial::Fleet;
use crate::serve::ServeGateway;

/// Largest single fill: the default pipe capacity, so one source→pipe fill is
/// always drainable by the pipe→destination drain. Identical to the blocking
/// shell's `SPLICE_CHUNK` and the proof's positive `chunk`.
const SPLICE_CHUNK: u32 = 64 * 1024;

/// Ring depth. Each live flow holds at most two in-flight SQEs (one per
/// direction), plus the standing accept, so this bounds concurrent flows before
/// the submission queue backs up into the software backlog.
const RING_ENTRIES: u32 = 4096;

/// How long to wait dialling the chosen upstream before giving up. Matches the
/// blocking shell.
const DIAL_TIMEOUT: Duration = Duration::from_secs(5);

/// Cap the completion wait so the `SHUTDOWN` flag is observed promptly even with
/// no flows posting anything.
const WAIT_CAP_NS: u32 = 200_000_000;

/// Splice flags for every fill and drain: hand the pages over (`MOVE`) and hint
/// that more of the stream follows (`MORE`), exactly as the blocking relay does.
const SPLICE_FLAGS: u32 = (libc::SPLICE_F_MOVE | libc::SPLICE_F_MORE) as u32;

/// Standing-accept completion tag. Distinct from every flow user_data, which is
/// `(slot << 1) | dir` and so never sets the high bit.
const ACCEPT_UD: u64 = 1 << 63;

/// One direction of a flow: the lockstep fill/drain state machine over one pipe.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Phase {
    /// Next completion is a source→pipe fill.
    Fill,
    /// Next completion is a pipe→destination drain of `pending` bytes.
    Drain,
}

/// One direction's live state — the running counterpart of the proof's per-channel
/// `pull chunk ; push chunk` iteration.
struct Dir {
    /// Source socket fd (bytes flow FROM here).
    src: RawFd,
    /// Destination socket fd (bytes flow TO here).
    dst: RawFd,
    /// Read end of this direction's private pipe (drain reads from here).
    pipe_r: RawFd,
    /// Write end of this direction's private pipe (fill writes to here).
    pipe_w: RawFd,
    /// What the next completion for this direction means.
    phase: Phase,
    /// Bytes buffered in the pipe awaiting drain (the `push chunk` amount).
    pending: u32,
    /// This direction has reached EOF (or failed); no SQE is in flight for it.
    done: bool,
}

/// One accepted passthrough connection: the client and upstream sockets, and the
/// two independent directions (`dirs[0]` = client→upstream, `dirs[1]` =
/// upstream→client).
struct Flow {
    /// Owned client socket; dropped (closed) when the flow is removed.
    _client: TcpStream,
    /// Owned upstream socket; dropped (closed) when the flow is removed.
    _upstream: TcpStream,
    dirs: [Dir; 2],
}

impl Drop for Flow {
    fn drop(&mut self) {
        // The four pipe ends are the only fds this struct owns raw; the two
        // sockets close via their `TcpStream` drops. A flow is only ever dropped
        // once both directions are `done`, so nothing is in flight over these.
        for d in &self.dirs {
            unsafe {
                libc::close(d.pipe_r);
                libc::close(d.pipe_w);
            }
        }
    }
}

/// The single-shard reactor state.
struct Reactor {
    ring: IoUring,
    listener_fd: RawFd,
    fleet: Arc<Fleet>,
    gw: ServeGateway,
    reply_tx: Sender<PooledBuf>,
    reply_rx: Receiver<PooledBuf>,
    /// Flow slab, indexed by slot; `None` slots are free.
    flows: Vec<Option<Flow>>,
    /// Free slot indices for reuse.
    free: Vec<usize>,
    /// SQEs awaiting room in the submission queue.
    backlog: Vec<squeue::Entry>,
}

/// Pack a flow's completion tag: `slot` in the high bits, the direction (0/1) in
/// bit 0. Never sets bit 63, so it is disjoint from [`ACCEPT_UD`].
#[inline]
fn dir_ud(slot: usize, dir: usize) -> u64 {
    ((slot as u64) << 1) | (dir as u64)
}

/// A source→pipe fill SQE for one direction (the proof's `pull chunk`).
fn fill_sqe(d: &Dir, ud: u64) -> squeue::Entry {
    opcode::Splice::new(types::Fd(d.src), -1, types::Fd(d.pipe_w), -1, SPLICE_CHUNK)
        .flags(SPLICE_FLAGS)
        .build()
        .user_data(ud)
}

/// A pipe→destination drain SQE for one direction, of exactly `len` bytes (the
/// proof's `push chunk`, sized to what the fill produced).
fn drain_sqe(d: &Dir, ud: u64, len: u32) -> squeue::Entry {
    opcode::Splice::new(types::Fd(d.pipe_r), -1, types::Fd(d.dst), -1, len)
        .flags(SPLICE_FLAGS)
        .build()
        .user_data(ud)
}

/// The standing accept SQE on the L4 listener.
fn accept_sqe(listener_fd: RawFd) -> squeue::Entry {
    opcode::Accept::new(
        types::Fd(listener_fd),
        std::ptr::null_mut(),
        std::ptr::null_mut(),
    )
    .build()
    .user_data(ACCEPT_UD)
}

/// Create one `O_CLOEXEC` pipe; `(read_end, write_end)` or `None` on failure.
fn make_pipe() -> Option<(RawFd, RawFd)> {
    let mut fds = [0i32; 2];
    if unsafe { libc::pipe2(fds.as_mut_ptr(), libc::O_CLOEXEC) } != 0 {
        return None;
    }
    Some((fds[0], fds[1]))
}

impl Reactor {
    /// Allocate a slot for `flow`, returning its index.
    fn insert_flow(&mut self, flow: Flow) -> usize {
        if let Some(slot) = self.free.pop() {
            self.flows[slot] = Some(flow);
            slot
        } else {
            self.flows.push(Some(flow));
            self.flows.len() - 1
        }
    }

    /// Free `slot` (dropping the flow: closing its sockets and pipes).
    fn remove_flow(&mut self, slot: usize) {
        if slot < self.flows.len() && self.flows[slot].take().is_some() {
            self.free.push(slot);
        }
    }

    /// Handle a completed accept: adopt the new client socket, choose and dial the
    /// proven upstream, and arm both directions' first fill. Then re-arm accept.
    fn on_accept(&mut self, res: i32) {
        // Re-arm the standing accept first, unconditionally, so the listener keeps
        // taking connections regardless of this one's fate.
        self.backlog.push(accept_sqe(self.listener_fd));

        if res < 0 {
            return; // transient accept error; the re-armed accept carries on
        }
        let client = unsafe { TcpStream::from_raw_fd(res) };
        self.begin_flow(client);
    }

    /// Choose the upstream (proven `drorb_proxy_pick`), dial it, wire the pipes,
    /// and submit each direction's opening fill. On no eligible backend or a dial
    /// failure the client is closed and nothing is dialled — the host meaning of
    /// `L4.accept_none_closes`.
    fn begin_flow(&mut self, client: TcpStream) {
        let peer = client.peer_addr().ok();
        let key = crate::l4::affinity_key(peer);
        let id = match crate::l4::pick_via_seam(
            self.fleet.mask(),
            &key,
            &self.gw,
            &self.reply_tx,
            &self.reply_rx,
        ) {
            Some(id) => id,
            None => {
                let _ = client.shutdown(Shutdown::Both);
                return;
            }
        };
        let addr: SocketAddr = match self.fleet.addr(id) {
            Some(a) => a,
            None => {
                let _ = client.shutdown(Shutdown::Both);
                return;
            }
        };
        let upstream = match TcpStream::connect_timeout(&addr, DIAL_TIMEOUT) {
            Ok(u) => u,
            Err(_) => {
                let _ = client.shutdown(Shutdown::Both);
                return;
            }
        };
        let _ = client.set_nodelay(true);
        let _ = upstream.set_nodelay(true);

        let (c2u_r, c2u_w) = match make_pipe() {
            Some(p) => p,
            None => {
                let _ = client.shutdown(Shutdown::Both);
                let _ = upstream.shutdown(Shutdown::Both);
                return;
            }
        };
        let (u2c_r, u2c_w) = match make_pipe() {
            Some(p) => p,
            None => {
                unsafe {
                    libc::close(c2u_r);
                    libc::close(c2u_w);
                }
                let _ = client.shutdown(Shutdown::Both);
                let _ = upstream.shutdown(Shutdown::Both);
                return;
            }
        };

        let cfd = client.as_raw_fd();
        let ufd = upstream.as_raw_fd();
        let flow = Flow {
            _client: client,
            _upstream: upstream,
            dirs: [
                // client → upstream
                Dir {
                    src: cfd,
                    dst: ufd,
                    pipe_r: c2u_r,
                    pipe_w: c2u_w,
                    phase: Phase::Fill,
                    pending: 0,
                    done: false,
                },
                // upstream → client
                Dir {
                    src: ufd,
                    dst: cfd,
                    pipe_r: u2c_r,
                    pipe_w: u2c_w,
                    phase: Phase::Fill,
                    pending: 0,
                    done: false,
                },
            ],
        };
        let slot = self.insert_flow(flow);
        // Open both directions' first fill: the proof's first `pull chunk` per lane.
        // Build the SQEs under a scoped borrow, then push (releases `self.flows`).
        let (s0, s1) = {
            let f = self.flows[slot].as_ref().unwrap();
            (
                fill_sqe(&f.dirs[0], dir_ud(slot, 0)),
                fill_sqe(&f.dirs[1], dir_ud(slot, 1)),
            )
        };
        self.backlog.push(s0);
        self.backlog.push(s1);
    }

    /// Advance one direction's lockstep state machine on its completion. This is
    /// the running heart of the proof's iteration: a fill completion carries the
    /// filled count and arms the matching drain; a drain completion (of the whole
    /// pending amount) re-arms the next fill; a fill of 0 is source EOF.
    fn on_flow(&mut self, slot: usize, dir: usize, res: i32) {
        let ud = dir_ud(slot, dir);
        // Advance the direction under a scoped borrow of the flow, yielding the
        // next SQE (if any) and whether the whole flow is now finished. The borrow
        // is released before touching `self.backlog` / freeing the slot.
        let (next, both_done) = {
            let flow = match self.flows.get_mut(slot).and_then(|f| f.as_mut()) {
                Some(f) => f,
                None => return, // flow already torn down
            };
            let d = &mut flow.dirs[dir];
            if d.done {
                return;
            }

            let next: Option<squeue::Entry> = if res == -libc::EAGAIN {
                // Would-block: the kernel could not make progress without waiting
                // past the async point; re-submit the identical op. (Rare for
                // blocking-mode fds, but handled so a spurious EAGAIN never wedges
                // a direction.)
                Some(match d.phase {
                    Phase::Fill => fill_sqe(d, ud),
                    Phase::Drain => drain_sqe(d, ud, d.pending),
                })
            } else {
                match d.phase {
                    Phase::Fill => {
                        if res == 0 {
                            // Source EOF: half-close the destination's write half so
                            // the peer sees the close; this direction is finished.
                            unsafe {
                                libc::shutdown(d.dst, libc::SHUT_WR);
                            }
                            d.done = true;
                            None
                        } else if res < 0 {
                            d.done = true; // fill error: fails, closed on teardown
                            None
                        } else {
                            d.pending = res as u32;
                            d.phase = Phase::Drain;
                            Some(drain_sqe(d, ud, d.pending))
                        }
                    }
                    Phase::Drain => {
                        if res <= 0 {
                            d.done = true; // destination closed / errored mid-drain
                            None
                        } else {
                            let moved = res as u32;
                            if moved >= d.pending {
                                // Whole fill drained: the pipe is empty again — the
                                // next `pull`.
                                d.pending = 0;
                                d.phase = Phase::Fill;
                                Some(fill_sqe(d, ud))
                            } else {
                                // Short drain (destination socket buffer full): push
                                // the rest before the next fill, so the pipe empties
                                // exactly — the lockstep invariant the proof requires.
                                d.pending -= moved;
                                Some(drain_sqe(d, ud, d.pending))
                            }
                        }
                    }
                }
            };
            (next, flow.dirs[0].done && flow.dirs[1].done)
        };
        if let Some(sqe) = next {
            self.backlog.push(sqe);
        }
        // Both directions finished ⇒ reclaim the flow (closes sockets + pipes).
        if both_done {
            self.remove_flow(slot);
        }
    }

    /// Push as many backlogged SQEs into the submission queue as fit, submitting to
    /// free room when it is full. Identical discipline to the serve reactor's flush.
    fn flush(&mut self) -> std::io::Result<()> {
        while !self.backlog.is_empty() {
            let mut pushed = 0;
            {
                let mut sq = self.ring.submission();
                for e in self.backlog.iter() {
                    // SAFETY: every fd an SQE references (client/upstream socket,
                    // pipe end) lives in its `Flow`, which is only freed once both
                    // directions are `done` — after which no SQE for it is armed.
                    // The listener fd outlives the reactor.
                    if unsafe { sq.push(e) }.is_err() {
                        break;
                    }
                    pushed += 1;
                }
            }
            self.backlog.drain(..pushed);
            if pushed == 0 {
                self.ring.submit()?;
            }
        }
        Ok(())
    }

    /// The shard loop: flush, wait (capped) for completions, reap the batch,
    /// repeat — until `SHUTDOWN`.
    fn run(&mut self) -> std::io::Result<()> {
        self.backlog.push(accept_sqe(self.listener_fd));
        loop {
            if crate::SHUTDOWN.load(Ordering::SeqCst) {
                return Ok(());
            }
            self.flush()?;
            let ts = types::Timespec::new().nsec(WAIT_CAP_NS);
            let args = types::SubmitArgs::new().timespec(&ts);
            match self.ring.submitter().submit_with_args(1, &args) {
                Ok(_) => {}
                Err(ref e) if e.raw_os_error() == Some(libc::ETIME) => {}
                Err(ref e) if e.raw_os_error() == Some(libc::EINTR) => {
                    if crate::SHUTDOWN.load(Ordering::SeqCst) {
                        return Ok(());
                    }
                    continue;
                }
                Err(e) => return Err(e),
            }
            let batch: Vec<(u64, i32)> = self
                .ring
                .completion()
                .map(|c| (c.user_data(), c.result()))
                .collect();
            for (ud, res) in batch {
                if ud == ACCEPT_UD {
                    self.on_accept(res);
                } else {
                    let slot = (ud >> 1) as usize;
                    let dir = (ud & 1) as usize;
                    self.on_flow(slot, dir, res);
                }
            }
        }
    }
}

/// Bind `listen_addr` and drive every L4 passthrough flow on ONE io_uring shard,
/// splicing bytes kernel-side via `IORING_OP_SPLICE` in the proven lockstep
/// fill/drain schedule. Returns `true` if it bound and ran (until shutdown),
/// `false` if the ring or the bind could not be set up — in which case the caller
/// falls back to the portable blocking pump.
pub fn run(listen_addr: &str, fleet: Arc<Fleet>, gw: ServeGateway) -> bool {
    let ring = match IoUring::new(RING_ENTRIES) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("dataplane: L4 io_uring init failed ({e}); using blocking splice");
            return false;
        }
    };
    let listener = match TcpListener::bind(listen_addr) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("dataplane: L4 TCP bind {listen_addr} failed: {e}");
            return true; // bind itself failed: nothing to fall back to
        }
    };
    let local = listener
        .local_addr()
        .map(|a| a.to_string())
        .unwrap_or_else(|_| listen_addr.to_string());
    eprintln!(
        "dataplane: listening on {local} (L4 raw-TCP passthrough via io_uring SPLICE; upstream = proven drorb_proxy_pick, bytes spliced verbatim in the proven lockstep fill/drain)"
    );
    let listener_fd = listener.as_raw_fd();
    let (reply_tx, reply_rx) = std::sync::mpsc::channel::<PooledBuf>();
    let mut reactor = Reactor {
        ring,
        listener_fd,
        fleet,
        gw,
        reply_tx,
        reply_rx,
        flows: Vec::new(),
        free: Vec::new(),
        backlog: Vec::new(),
    };
    if let Err(e) = reactor.run() {
        eprintln!("dataplane: L4 io_uring shard error: {e}");
    }
    // Keep the listener alive for the whole reactor lifetime.
    drop(listener);
    true
}
