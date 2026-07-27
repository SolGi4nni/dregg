//! The multi-worker supervisor (`--workers N`).
//!
//! The proven serve is a process-global singleton: one Lean runtime, one serve
//! thread per process (see `serve`). Many IO shards feed that one thread, so a
//! single process's request throughput is capped by one core's worth of serve
//! latency. The share-nothing way past that ceiling is more *processes*: N
//! independent copies of this binary, each with its own runtime and serve thread,
//! all bound to the one port with `SO_REUSEPORT`. The kernel then load-balances
//! incoming connections across them — on Linux and the BSDs it hash-distributes
//! across every `SO_REUSEPORT` socket, including across processes, so throughput
//! scales ~Nx. (Darwin only *permits* the duplicate bind; it does not
//! cross-distribute, so there the operator needs a front load balancer.)
//!
//! This is a pure shell change with zero proof impact: every worker runs the same
//! `drorb_serve`, byte-for-byte, exactly as the single-process path does. The
//! parent never boots a runtime — it only spawns, supervises, and tears down the
//! workers. `--workers 1` (the default) skips this module entirely.

use std::process::{Child, Command};
use std::sync::atomic::Ordering;
use std::time::Duration;

/// POSIX `SIGTERM`; the supervisor treats it the same as `SIGINT`.
const SIGTERM: i32 = 15;

/// The parent argv to hand each worker: the original arguments with the
/// `--workers`/`-w` flag (and its count) removed, so a worker re-enters `main`
/// on the ordinary single-process path.
fn worker_args() -> Vec<String> {
    let mut out = Vec::new();
    let mut it = std::env::args().skip(1);
    while let Some(a) = it.next() {
        match a.as_str() {
            "--workers" | "-w" => {
                let _ = it.next(); // drop the count argument too
            }
            _ => out.push(a),
        }
    }
    out
}

/// Become the multi-worker supervisor: spawn `n` worker processes sharing the
/// one `SO_REUSEPORT` port, then supervise them until a shutdown signal. Reaps
/// and respawns a worker that dies. Never returns — it `exit`s the process on
/// shutdown.
pub fn supervise(n: usize) {
    // A shutdown signal (SIGINT or SIGTERM) sets the shared flag; the loop below
    // observes it and tears the workers down.
    // SAFETY: `on_sigint` only stores into an atomic — async-signal-safe.
    unsafe {
        crate::signal(crate::SIGINT, crate::on_sigint as *const () as usize);
        crate::signal(SIGTERM, crate::on_sigint as *const () as usize);
    }

    let exe = std::env::current_exe().unwrap_or_else(|e| {
        eprintln!("dataplane: --workers cannot find own executable: {e}");
        std::process::exit(1);
    });
    let child_args = worker_args();
    let spawn_one = || -> std::io::Result<Child> {
        Command::new(&exe)
            .args(&child_args)
            // Mark the child so it runs the single-process serve path, not the
            // supervisor, however DRORB_WORKERS/--workers was passed through.
            .env("DRORB_WORKER", "1")
            .spawn()
    };

    let mut children: Vec<Child> = Vec::with_capacity(n);
    for i in 0..n {
        match spawn_one() {
            Ok(c) => children.push(c),
            Err(e) => eprintln!("dataplane: worker {i} spawn failed: {e}"),
        }
    }
    if children.is_empty() {
        eprintln!("dataplane: --workers spawned no workers; nothing to serve");
        std::process::exit(1);
    }
    eprintln!(
        "dataplane: supervising {} workers behind the shared SO_REUSEPORT port \
         (each its own proven runtime; SIGINT to stop)",
        children.len()
    );

    // Per-slot restart bookkeeping, one entry per worker slot.
    let mut state: Vec<SlotState> = (0..children.len()).map(|_| SlotState::new()).collect();
    // A slot awaiting its backoff holds no live child; `Slot` models that.
    let mut slots: Vec<Slot> = children.into_iter().map(Slot::Running).collect();

    loop {
        if crate::SHUTDOWN.load(Ordering::SeqCst) {
            for s in slots.iter_mut() {
                if let Slot::Running(c) = s {
                    let _ = c.kill();
                }
            }
            for s in slots.iter_mut() {
                if let Slot::Running(c) = s {
                    let _ = c.wait();
                }
            }
            eprintln!("dataplane: all workers stopped");
            std::process::exit(0);
        }
        let now = std::time::Instant::now();
        for (i, slot) in slots.iter_mut().enumerate() {
            match slot {
                // Reap a worker that exited on its own (a crash — including the
                // serve owner's `exit(70)` crash-only path — not a supervised
                // shutdown) and schedule its respawn under backoff.
                Slot::Running(child) => match child.try_wait() {
                    Ok(Some(status)) => {
                        if crate::SHUTDOWN.load(Ordering::SeqCst) {
                            continue;
                        }
                        let st = &mut state[i];
                        st.record_exit(now);
                        if st.budget_exhausted() {
                            eprintln!(
                                "dataplane: worker {i} exited ({status}) and has burned its \
                                 restart budget ({MAX_RESTARTS} restarts in {}s) — GIVING UP on \
                                 this slot. A worker that keeps dying immediately is a real \
                                 defect (bad config, unservable port, a panic on every request); \
                                 respawning it forever would only hide that.",
                                RESTART_WINDOW.as_secs()
                            );
                            *slot = Slot::Abandoned;
                            continue;
                        }
                        eprintln!(
                            "dataplane: worker {i} exited ({status}); respawning in {}ms \
                             (restart {} of {MAX_RESTARTS} in this {}s window)",
                            st.backoff.as_millis(),
                            st.exits.len(),
                            RESTART_WINDOW.as_secs()
                        );
                        *slot = Slot::Waiting(now + st.backoff);
                    }
                    Ok(None) => {}
                    Err(e) => eprintln!("dataplane: worker {i} wait error: {e}"),
                },
                // Backoff elapsed: bring the slot back.
                Slot::Waiting(at) if now >= *at => match spawn_one() {
                    Ok(c) => {
                        eprintln!("dataplane: worker {i} respawned");
                        *slot = Slot::Running(c);
                    }
                    Err(e) => {
                        // Spawn itself failed; back off again rather than
                        // hot-looping on whatever is denying the spawn.
                        let st = &mut state[i];
                        st.record_exit(now);
                        eprintln!(
                            "dataplane: worker {i} respawn failed: {e}; retrying in {}ms",
                            st.backoff.as_millis()
                        );
                        *slot = Slot::Waiting(now + st.backoff);
                    }
                },
                Slot::Waiting(_) | Slot::Abandoned => {}
            }
        }
        // If every slot has been abandoned there is nothing serving and nothing
        // that will ever serve again. Exit non-zero so the OUTER supervisor
        // (systemd `Restart=on-failure`, or an operator) sees a failed unit
        // instead of a live supervisor process quietly supervising nothing —
        // the same silent-wedge rule the serve owner follows.
        if slots.iter().all(|s| matches!(s, Slot::Abandoned)) {
            eprintln!(
                "dataplane: FATAL — every worker slot abandoned after repeated crashes; \
                 nothing is serving. Exiting 70 for the outer supervisor."
            );
            std::process::exit(70);
        }
        std::thread::sleep(Duration::from_millis(200));
    }
}

/// Maximum worker restarts per slot inside [`RESTART_WINDOW`] before the
/// supervisor stops trying (a restart *budget*, not an unbounded retry).
const MAX_RESTARTS: usize = 10;

/// The sliding window the restart budget is counted over.
const RESTART_WINDOW: Duration = Duration::from_secs(60);

/// First respawn delay; doubles per consecutive crash up to [`BACKOFF_MAX`].
const BACKOFF_MIN: Duration = Duration::from_millis(200);

/// Ceiling on the exponential respawn backoff.
const BACKOFF_MAX: Duration = Duration::from_secs(30);

/// One supervised worker slot.
enum Slot {
    /// A live worker process.
    Running(Child),
    /// The worker died; respawn once this instant is reached (backoff).
    Waiting(std::time::Instant),
    /// The worker burned its restart budget; the supervisor stopped retrying.
    Abandoned,
}

/// Per-slot crash history driving backoff and the restart budget.
struct SlotState {
    /// Exit instants inside the current window, oldest first.
    exits: Vec<std::time::Instant>,
    /// The delay before the NEXT respawn of this slot.
    backoff: Duration,
}

impl SlotState {
    fn new() -> Self {
        SlotState {
            exits: Vec::new(),
            backoff: BACKOFF_MIN,
        }
    }

    /// Record a crash at `now`: drop exits that have aged out of the window and
    /// grow the backoff. A slot that has been healthy for a full window has an
    /// empty history, so its backoff resets to the minimum — a rare crash after
    /// a long healthy run restarts fast; a crash LOOP slows down.
    fn record_exit(&mut self, now: std::time::Instant) {
        self.exits
            .retain(|t| now.duration_since(*t) < RESTART_WINDOW);
        if self.exits.is_empty() {
            self.backoff = BACKOFF_MIN;
        } else {
            self.backoff = (self.backoff * 2).min(BACKOFF_MAX);
        }
        self.exits.push(now);
    }

    fn budget_exhausted(&self) -> bool {
        self.exits.len() > MAX_RESTARTS
    }
}
