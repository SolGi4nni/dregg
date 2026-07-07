//! Runtime reconfiguration on SIGHUP — the untrusted shell that EXECUTES the
//! proven graceful-drain DECISION when the operator config changes.
//!
//! On `SIGHUP` the host re-reads `DRORB_CONFIG`, re-parses it through the proven
//! parser (`config::reload` → `drorb_deployment_of_config`), and — only if it
//! parses — atomically swaps in the new deployment for every subsequent request.
//! A parse failure keeps the running config (fail-safe). No connection is
//! dropped: a request already in flight holds its own `Arc` snapshot of the old
//! deployment (`config::get`) and finishes under it; the next request picks up
//! the new one.
//!
//! ## Correspondence to the proven `Drain` (`Drain.step` / `DrainContract`)
//!
//! The proven model in `Drain.Basic` / `DrainCorrect` is a lifecycle transition
//! system whose `Drain.step` decides, per event, whether a new connection is
//! ADMITTED and when the old lifecycle has DRAINED. `DrainCorrect.drain_refines_spec`
//! proves `Drain.step` (as `DrainImpl`) satisfies `DrainContract`:
//!
//!   * `noAdmitAfterSignal` — once the drain signal has fired, no `acceptReq` is
//!     `admitted`;
//!   * `neverDrainedWithWork` — the `drained` terminal is never observed while
//!     the in-flight count is positive;
//!   * `drainCompletes` — a lifecycle in the drain window whose in-flight count
//!     has reached zero HAS drained (progress).
//!
//! This module is the untrusted shell that carries out that decision for a
//! config generation. Treat each generation of the deployment as one `Drain`
//! lifecycle. A SIGHUP that installs generation `g+1` is the `beginDrain` event
//! for generation `g`:
//!
//!   * `beginDrain` / `noAdmitAfterSignal`: after the swap, NO new request is
//!     served under the old config — the `RwLock` publish means every subsequent
//!     `config::get` returns generation `g+1`. New work is admitted only under
//!     the new generation, exactly as `Drain.step` refuses every `acceptReq`
//!     after the signal.
//!   * `live` / in-flight: the number of requests still holding an `Arc` to
//!     generation `g` is that lifecycle's `inflight`. The `Arc` refcount is the
//!     concrete `live` witness — the old deployment object stays alive precisely
//!     while a straggler references it.
//!   * `neverDrainedWithWork` + `drainCompletes`: generation `g` is `drained`
//!     exactly when its last in-flight request completes and drops the last
//!     `Arc` (the object is freed) — never earlier (no request is cut off
//!     mid-flight) and always once the last finishes (progress). That is the
//!     `drained ⇔ inflight = 0` biconditional (`drainImpl_drained_iff_idle`).
//!
//! We do not re-derive those facts here — they are proved in `DrainCorrect`. The
//! shell only performs the `beginDrain` swap and lets the language runtime's
//! refcount drain the old generation; the DECISION (admit only under the new
//! generation, never drop an in-flight request) is the proven one.

use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::time::Duration;

use crate::config::ReloadOutcome;
use crate::serve::ServeGateway;

/// Set by the async-signal-safe SIGHUP handler; drained by the watcher thread.
static RELOAD_PENDING: AtomicBool = AtomicBool::new(false);
/// True for the duration of a reconfig swap; surfaced (with `DRAIN_BEGUN`) as
/// `drorb_draining`.
static DRAINING: AtomicBool = AtomicBool::new(false);
/// Set once an operator has begun a graceful drain (`POST /admin/drain`) and left
/// standing: the `beginDrain` lifecycle event carried out of band. Unlike the
/// transient swap `DRAINING`, this stays set — it stops the host advertising
/// readiness (`/healthz` → 503) so a fronting balancer bleeds new traffic away
/// while in-flight requests finish untouched.
static DRAIN_BEGUN: AtomicBool = AtomicBool::new(false);
static RELOADS_APPLIED: AtomicU64 = AtomicU64::new(0);
static RELOADS_REJECTED: AtomicU64 = AtomicU64::new(0);

const SIGHUP: i32 = 1;

unsafe extern "C" {
    fn signal(signum: i32, handler: usize) -> usize;
}

/// The SIGHUP handler: async-signal-safe (a single atomic store). The actual
/// re-read/re-parse/swap runs off-signal on the watcher thread.
extern "C" fn on_sighup(_sig: i32) {
    RELOAD_PENDING.store(true, Ordering::SeqCst);
}

/// Reconfigs successfully applied so far.
pub fn reloads_applied() -> u64 {
    RELOADS_APPLIED.load(Ordering::SeqCst)
}

/// Reconfigs rejected (fail-safe kept the old config) so far.
pub fn reloads_rejected() -> u64 {
    RELOADS_REJECTED.load(Ordering::SeqCst)
}

/// Whether the host is draining: either a reconfig swap is in progress, or an
/// operator has begun a graceful drain (`begin_drain`). Surfaced as
/// `drorb_draining`.
pub fn draining() -> bool {
    DRAINING.load(Ordering::SeqCst) || DRAIN_BEGUN.load(Ordering::SeqCst)
}

/// Whether an operator has begun a standing graceful drain (`POST /admin/drain`).
/// `/healthz` reads this to advertise 503 so a fronting balancer stops sending
/// new work here; in-flight requests keep their own config `Arc` and finish.
pub fn drain_begun() -> bool {
    DRAIN_BEGUN.load(Ordering::SeqCst)
}

/// Begin a standing graceful drain: the operator-initiated `beginDrain` event.
/// Sets the drain flag (idempotent — a second call is a no-op) so `/healthz`
/// flips to 503 and no fresh readiness is advertised, while every in-flight
/// request finishes under the config it started on. This is the same
/// `beginDrain`/no-admit decision the reconfig swap carries (see the module doc's
/// correspondence to the proven `Drain`), applied to the whole host rather than a
/// single config generation. Returns `true` if this call started the drain,
/// `false` if a drain was already in progress.
pub fn begin_drain() -> bool {
    let already = DRAIN_BEGUN.swap(true, Ordering::SeqCst);
    if !already {
        let inflight = crate::ACTIVE_CONNS.load(Ordering::SeqCst);
        eprintln!(
            "dataplane: graceful DRAIN begun — /healthz now advertises 503; no new readiness \
             is offered, {inflight} in-flight request(s) finish under their own config \
             (proven Drain: beginDrain — no new admit, in-flight complete)"
        );
    }
    !already
}

/// Install the SIGHUP handler and spawn the watcher thread that performs the
/// reload off-signal. Idempotent enough to call once at boot after the serve
/// gateway and boot config are up.
pub fn install(gw: ServeGateway) {
    // SAFETY: `on_sighup` only stores into an atomic — async-signal-safe;
    // installing it at boot is standard.
    unsafe { signal(SIGHUP, on_sighup as *const () as usize) };
    std::thread::Builder::new()
        .name("drorb-reconfig".into())
        .spawn(move || watch(gw))
        .expect("failed to spawn the reconfig watcher thread");
}

/// The watcher loop: on a pending SIGHUP, perform the reload. Exits on shutdown.
fn watch(gw: ServeGateway) {
    loop {
        if crate::SHUTDOWN.load(Ordering::SeqCst) {
            return;
        }
        if RELOAD_PENDING.swap(false, Ordering::SeqCst) {
            apply(&gw);
        }
        std::thread::sleep(Duration::from_millis(100));
    }
}

/// The SIGHUP watcher's reconfig step: perform one reload and discard the
/// outcome (it has already been logged and counted by `reload_now`).
fn apply(gw: &ServeGateway) {
    let _ = reload_now(gw, "SIGHUP");
}

/// Perform one reconfig now and RETURN its outcome: re-parse `DRORB_CONFIG` and,
/// if it parses, execute the `beginDrain`/swap decision, bumping the
/// applied/rejected counters and logging. In-flight requests under the old
/// generation are the drain window (see the module doc); they finish untouched.
///
/// Shared by the SIGHUP watcher and the out-of-band `POST /admin/reload`, so the
/// admin reload takes the SAME proven-parser re-read + atomic swap as a signal —
/// `origin` only tags the log line. Callable from any thread (the parse itself is
/// marshalled onto the runtime-owner thread through `gw`).
pub fn reload_now(gw: &ServeGateway, origin: &str) -> ReloadOutcome {
    // The in-flight count at the swap point — this generation's `live` stragglers
    // that will drain out under the old config.
    let inflight = crate::ACTIVE_CONNS.load(Ordering::SeqCst);
    DRAINING.store(true, Ordering::SeqCst);
    let outcome = crate::config::reload(gw);
    match &outcome {
        ReloadOutcome::Applied { generation } => {
            RELOADS_APPLIED.fetch_add(1, Ordering::SeqCst);
            eprintln!(
                "dataplane: {origin} reconfig APPLIED — config generation {generation}; new connections \
                 use gen {generation}, {inflight} in-flight connection(s) drain under the old config \
                 (proven Drain: beginDrain — no new admit under the old gen, in-flight complete)"
            );
        }
        ReloadOutcome::KeptOld { reason } => {
            RELOADS_REJECTED.fetch_add(1, Ordering::SeqCst);
            eprintln!(
                "dataplane: {origin} reconfig REJECTED — keeping the running config (fail-safe): {reason}"
            );
        }
        ReloadOutcome::NoConfig => {
            eprintln!("dataplane: {origin} reconfig requested but DRORB_CONFIG is unset — nothing to reload");
        }
    }
    DRAINING.store(false, Ordering::SeqCst);
    outcome
}
