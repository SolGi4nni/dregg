//! The HOUYHNHNM RECOVERY MONITOR — an external, simple-but-complete watcher
//! that reads the LIVE ARTIFACT (never a self-reported "OK"), detects
//! claimed-vs-actual divergence, and can stop / inspect / restart a wedged
//! subsystem. Recursive: a monitor can itself be the subsystem another monitor
//! watches.
//!
//! ## What this is (fare's Houyhnhnm Computing, ch3 + ch6)
//!
//! `docs/deos/HOUYHNHNM-CONVERGENCE.md` names "The Monitor" as the standout
//! Houyhnhnm principle dregg has the SUBSTRATE for but not yet the FEATURE:
//!
//! > an external, simple-but-complete watcher that reads the **live artifact**
//! > (never a self-reported "OK"), detects claimed-vs-actual divergence (the
//! > council's `RECOVERY_NOT_HOLDING`), and can stop / inspect / fix / restart a
//! > wedged subsystem — recursively (a monitor of monitors).
//!
//! This module is that monitor. It is deliberately the firmament's SIMPLEST
//! component — a few hundred lines, no async, no I/O of its own — because a
//! monitor that is itself complex cannot be trusted to recover a complex thing.
//! (ch6's polycentric kernel: each subsystem its own kernel; the monitor is the
//! tiny privileged watcher that does NOT trust the watched.)
//!
//! ## The keystone: artifact-over-assertion
//!
//! The root failure that burned the Lunar Town Council's buildr fleet for 15
//! hours was **assertion-over-artifact** — "a tool asserting success the live
//! artifact refutes" (`revert OK`, `refreshed=5` over dead tokens). A
//! restart-loop logged "revert OK" while the live artifact re-wedged every 4
//! minutes; nothing read the artifact, so nothing noticed.
//!
//! The structural fix here: the monitor NEVER reads the subsystem's CLAIM. It
//! reads the subsystem's [`Subsystem::probe`] — the **live artifact**: for a
//! confined host-PD, does the firmament Endpoint ACTUALLY round-trip right now?
//! When the subsystem (or a recovery action) CLAIMS `Healthy` but the probe says
//! `Wedged`, the monitor emits [`Divergence::RecoveryNotHolding`] — the
//! council's exact signal — and escalates. The claim is, at most, a HINT about
//! WHERE to look; it is never evidence of health. (ch2: "I object to doing
//! things computers can do" — the witness IS the truth, the computer verifies.)
//!
//! ## The four powers (the Monitor's verbs)
//!
//! 1. **WATCH** — [`Subsystem::probe`] reads the real state, returns
//!    [`ActualState`]. Generalized over the [`Subsystem`] trait so the same
//!    monitor watches a host-PD (Endpoint round-trip), a cell (real committed
//!    state), or a queue (real depth) — anything that can witness its own
//!    liveness. The host-PD adapter is [`HostPdSubsystem`] (feature `process-pd`).
//! 2. **DETECT divergence** — [`RecoveryMonitor::tick`] compares the CLAIM the
//!    subsystem reports against what the probe witnesses. Claim says recovered,
//!    probe says wedged ⇒ [`Divergence::RecoveryNotHolding`].
//! 3. **RESTART-LOOP detection** — a counter + window. If the subsystem
//!    re-wedges within [`MonitorPolicy::rewedge_window`] after a recovery, the
//!    [`RecoveryMonitor`] increments an attempt counter; after
//!    [`MonitorPolicy::max_attempts`] it ESCALATES ([`Verdict::Escalate`] with
//!    [`Escalation::RecoveryNotHolding`]) instead of looping forever. (The
//!    council invented exactly this counter under fire.)
//! 4. **ACT** — [`Subsystem::stop`] / [`Subsystem::restart`] drive the watched
//!    thing's lifecycle (for a host-PD: the [`crate::process_kernel`] PD
//!    lifecycle). **Fail-closed**: a restart is only [`Verdict::Recovered`] if a
//!    FRESH probe AFTER the restart witnesses health. If the post-restart probe
//!    still says wedged, the monitor NEVER claims success — it counts the attempt
//!    and re-enters the loop / escalates.
//!
//! ## Recursive (Houyhnhnm: virtualized monitors of monitors)
//!
//! A [`RecoveryMonitor`] is itself a [`Subsystem`] (via [`MonitorSubsystem`]):
//! its "live artifact" is *its own escalation state* (has it given up on its
//! charge?), and "restart" resets its attempt counter and re-attempts. So a
//! supervisory monitor can watch a fleet of monitors and recover a monitor that
//! itself gave up — turtles all the way up, each layer reading the layer below's
//! ARTIFACT, never its claim.

use std::string::String;

/// What the LIVE ARTIFACT actually witnesses about a subsystem RIGHT NOW. This
/// is read by [`Subsystem::probe`] from the real thing (an Endpoint round-trip,
/// a committed cell state, a queue depth) — NOT from any log or self-report.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ActualState {
    /// The live artifact witnesses health — e.g. the host-PD's firmament
    /// Endpoint round-tripped just now; the cell's committed state is the
    /// expected one; the queue is draining.
    Healthy,
    /// The live artifact witnesses a WEDGE — the Endpoint did not round-trip,
    /// the cell is stuck, the queue is not draining. Carries a short reason for
    /// the serial/audit log (the firmament's `note` discipline).
    Wedged(String),
}

impl ActualState {
    /// Did the live artifact witness health?
    pub fn is_healthy(&self) -> bool {
        matches!(self, ActualState::Healthy)
    }
    /// A wedge with `reason`.
    pub fn wedged(reason: impl Into<String>) -> Self {
        ActualState::Wedged(reason.into())
    }
}

/// What a subsystem (or a recovery action) CLAIMS about itself — the
/// self-report. **THIS IS NEVER TRUSTED AS EVIDENCE OF HEALTH.** It is at most a
/// hint about where to look; the monitor always cross-checks it against
/// [`ActualState`] from a real [`Subsystem::probe`]. The whole point of the
/// monitor is that a `Claim::Recovered` over a `ActualState::Wedged` artifact is
/// the wound it catches.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Claim {
    /// The subsystem (or a just-run recovery action) ASSERTS it is healthy /
    /// recovered — the `revert OK` log line. May be a lie the artifact refutes.
    Recovered,
    /// The subsystem makes no health claim (or admits it is broken).
    None,
}

/// The thing a [`RecoveryMonitor`] watches and can act on. The ONE abstraction
/// over "a confined host-PD", "a cell", "a queue", "another monitor".
///
/// The contract is the keystone:
/// - [`Self::probe`] reads the **LIVE ARTIFACT** — the real, current state.
///   It must NOT consult any cached claim/log; it must witness the actual thing.
/// - [`Self::claim`] returns what the subsystem SAYS about itself — explicitly
///   separated so the monitor can detect a divergence between the two.
/// - [`Self::stop`] / [`Self::restart`] are the lifecycle actions (for a
///   host-PD, the [`crate::process_kernel`] PD lifecycle).
pub trait Subsystem {
    /// Read the LIVE ARTIFACT and return what it actually witnesses NOW. This is
    /// the load-bearing method: it MUST reach the real thing (round-trip the
    /// Endpoint / read committed state / measure the queue), never a log.
    fn probe(&mut self) -> ActualState;

    /// What the subsystem CLAIMS about itself (the self-report; never trusted).
    /// Default: makes no claim — a subsystem that does not self-report cannot
    /// lie, which is the safest default.
    fn claim(&self) -> Claim {
        Claim::None
    }

    /// STOP the subsystem (quiesce it before a restart). For a host-PD this is
    /// the PD lifecycle stop. Returns whether stop was effected.
    fn stop(&mut self) -> bool;

    /// RESTART the subsystem (a fresh instance of the wedged thing). For a
    /// host-PD this re-spawns the confined child and re-registers its Endpoint.
    /// Returns whether a restart was effected. **The monitor does NOT trust this
    /// return** as proof of recovery — it always re-probes the live artifact.
    fn restart(&mut self) -> bool;

    /// A short human label for logs/escalation routing.
    fn label(&self) -> &str {
        "subsystem"
    }
}

/// A divergence the monitor DETECTED by reading the live artifact — the catch.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Divergence {
    /// **THE COUNCIL'S EXACT SIGNAL.** The subsystem (or a recovery action)
    /// CLAIMED `Recovered`, but the live-artifact probe witnesses a wedge. The
    /// `revert OK` over a re-wedged artifact, caught structurally because the
    /// monitor read the artifact, not the log. Carries the wedge reason the
    /// probe returned.
    RecoveryNotHolding {
        /// The wedge reason the live-artifact probe witnessed.
        artifact: String,
    },
}

/// Why the monitor ESCALATED (gave up the recovery loop and routed to a watcher
/// — a human, or a supervisory monitor). Escalation is fail-closed: the monitor
/// reaches it rather than ever claim a recovery the artifact does not support.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Escalation {
    /// The restart-loop guard tripped: the subsystem re-wedged within the window
    /// after `attempts` recovery attempts (≥ the policy's `max_attempts`). The
    /// council's `RECOVERY_NOT_HOLDING` — scream, route to a watcher, STOP
    /// looping. This is precisely the counter the council invented under fire to
    /// end a 15-hour restart-loop that would otherwise have run forever.
    RecoveryNotHolding {
        /// How many recovery attempts were made before giving up.
        attempts: u32,
        /// The most recent wedge reason the live-artifact probe witnessed.
        last_artifact: String,
    },
}

/// The verdict of one [`RecoveryMonitor::tick`] — what the monitor observed and
/// did this cycle. Always grounded in a LIVE-ARTIFACT probe.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Verdict {
    /// The live artifact witnesses health and the claim (if any) agrees. No
    /// action taken — the Houyhnhnm steady state.
    Healthy,
    /// A wedge was witnessed and a restart was attempted AND a FRESH post-restart
    /// probe witnessed health. Genuinely recovered (not claimed — witnessed).
    Recovered {
        /// How many attempts it took this episode (≥ 1).
        attempts: u32,
    },
    /// A divergence was detected: the claim said recovered, the artifact refutes
    /// it. The monitor will attempt recovery (or escalate if the loop guard
    /// trips). Carries the structural catch.
    Diverged(Divergence),
    /// The monitor gave up the recovery loop and escalated to a watcher — the
    /// fail-closed terminal of the restart-loop guard.
    Escalate(Escalation),
}

/// The monitor's policy — the restart-loop guard parameters the council
/// hard-won. Kept tiny and explicit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MonitorPolicy {
    /// How many recovery attempts to make before escalating (the council's
    /// counter). After this many attempts that each re-wedge within the window,
    /// the monitor emits [`Escalation::RecoveryNotHolding`] instead of looping.
    pub max_attempts: u32,
    /// The re-wedge window, in monitor TICKS. If the subsystem wedges again
    /// within this many ticks of a recovery attempt, the attempt is counted
    /// against the loop guard (a fast re-wedge is the loop signature). If it
    /// stays healthy LONGER than this window, the attempt counter resets — a
    /// recovery that actually held is forgiven.
    pub rewedge_window: u32,
}

impl Default for MonitorPolicy {
    /// A sane default: 3 attempts, re-wedge window of 4 ticks. (4 echoes the
    /// council's "re-wedged every 4 min" — a tick is the monitor's poll period.)
    fn default() -> Self {
        MonitorPolicy {
            max_attempts: 3,
            rewedge_window: 4,
        }
    }
}

/// THE MONITOR. An external watcher of ONE subsystem `S`. Simple-but-complete:
/// it watches (probe), detects (claim-vs-artifact), guards the restart loop
/// (counter + window), and acts (stop/restart) — fail-closed throughout.
///
/// Drive it by calling [`Self::tick`] on a period (the firmament's event loop, a
/// timer, or a test). Each tick reads the LIVE ARTIFACT and returns a
/// [`Verdict`]. The monitor never claims a recovery the artifact does not
/// support, and never loops forever — it escalates.
pub struct RecoveryMonitor<S: Subsystem> {
    subsystem: S,
    policy: MonitorPolicy,
    /// Recovery attempts made in the CURRENT episode (reset when a recovery is
    /// witnessed to HOLD past the re-wedge window). The council's counter.
    attempts: u32,
    /// Ticks since the last recovery attempt — used to decide whether a new
    /// wedge is a "re-wedge within the window" (counts against the guard) or a
    /// fresh, forgiven episode (resets the counter).
    ticks_since_attempt: u32,
    /// Once escalated, the monitor stays escalated until explicitly reset — it
    /// does NOT silently resume claiming health (fail-closed; a supervisory
    /// monitor must intervene). This is the artifact a parent monitor reads.
    escalated: bool,
}

impl<S: Subsystem> RecoveryMonitor<S> {
    /// A monitor of `subsystem` with `policy`.
    pub fn new(subsystem: S, policy: MonitorPolicy) -> Self {
        RecoveryMonitor {
            subsystem,
            policy,
            attempts: 0,
            ticks_since_attempt: u32::MAX, // not in any window initially
            escalated: false,
        }
    }

    /// A monitor with the default policy.
    pub fn with_default_policy(subsystem: S) -> Self {
        Self::new(subsystem, MonitorPolicy::default())
    }

    /// Has this monitor ESCALATED (given up the recovery loop)? This is the
    /// monitor's OWN live artifact — what a supervisory (recursive) monitor
    /// reads about it. While `true`, the monitor's charge is unrecovered.
    pub fn has_escalated(&self) -> bool {
        self.escalated
    }

    /// The recovery attempts made in the current episode (the loop-guard count).
    pub fn attempts(&self) -> u32 {
        self.attempts
    }

    /// Borrow the watched subsystem (e.g. for inspection — the Monitor's "inspect"
    /// power between stop and restart).
    pub fn subsystem(&self) -> &S {
        &self.subsystem
    }
    /// Mutably borrow the watched subsystem.
    pub fn subsystem_mut(&mut self) -> &mut S {
        &mut self.subsystem
    }

    /// RESET the monitor after a supervisory intervention — clears the escalation
    /// and the attempt counter so the recovery loop may run again. This is what a
    /// recursive parent monitor's `restart` of THIS monitor does. (We do NOT
    /// auto-clear escalation; a watcher must decide the underlying cause is
    /// addressed — fail-closed.)
    pub fn reset(&mut self) {
        self.escalated = false;
        self.attempts = 0;
        self.ticks_since_attempt = u32::MAX;
    }

    /// ONE monitor cycle. Reads the LIVE ARTIFACT, detects claim-vs-artifact
    /// divergence, and — if wedged — guards the restart loop and acts
    /// (stop→restart→FRESH re-probe), fail-closed. Returns the [`Verdict`].
    ///
    /// The control flow IS the Houyhnhnm monitor:
    ///
    /// 1. If already escalated, stay escalated (fail-closed; needs a [`reset`]).
    /// 2. Probe the live artifact. Note the claim, but NEVER trust it.
    /// 3. Artifact healthy:
    ///    - claim also healthy (or none) ⇒ [`Verdict::Healthy`]; if the recovery
    ///      held past the re-wedge window, reset the attempt counter.
    ///    - (a claim cannot "diverge" toward health it actually has — health is
    ///      witnessed, so a healthy artifact is simply healthy.)
    /// 4. Artifact WEDGED:
    ///    - if the claim says `Recovered`, that is the CATCH:
    ///      [`Divergence::RecoveryNotHolding`] — emit it, then proceed to recover.
    ///    - decide if this wedge is a re-wedge WITHIN the window (counts against
    ///      the guard) or a fresh episode (the counter was reset).
    ///    - if attempts already ≥ `max_attempts` ⇒ ESCALATE (stop the loop).
    ///    - else: stop → restart → FRESH probe. Recovery is claimed ONLY if the
    ///      fresh probe witnesses health; otherwise count the attempt and, if the
    ///      guard now trips, escalate.
    ///
    /// [`reset`]: Self::reset
    pub fn tick(&mut self) -> Verdict {
        // (1) Fail-closed: once escalated, stay escalated until a supervisory
        // reset. We re-report the escalation as the artifact a parent reads.
        if self.escalated {
            let last = match self.subsystem.probe() {
                ActualState::Wedged(r) => r,
                ActualState::Healthy => String::from("escalated (awaiting supervisory reset)"),
            };
            return Verdict::Escalate(Escalation::RecoveryNotHolding {
                attempts: self.attempts,
                last_artifact: last,
            });
        }

        // (2) Read the LIVE ARTIFACT. Capture the claim ONLY to cross-check it.
        let claim = self.subsystem.claim();
        let actual = self.subsystem.probe();

        // (3) Healthy artifact.
        if actual.is_healthy() {
            self.ticks_since_attempt = self.ticks_since_attempt.saturating_add(1);
            // A recovery that HELD past the re-wedge window is forgiven: reset
            // the loop guard so a future, unrelated wedge gets a fresh budget.
            if self.ticks_since_attempt > self.policy.rewedge_window {
                self.attempts = 0;
            }
            return Verdict::Healthy;
        }

        // (4) WEDGED artifact. First, the structural catch: a claim of recovery
        // over a wedged artifact is RecoveryNotHolding — the council's signal,
        // detected because we read the artifact, not the log.
        let artifact = match &actual {
            ActualState::Wedged(r) => r.clone(),
            ActualState::Healthy => unreachable!(),
        };
        let divergence_caught = matches!(claim, Claim::Recovered);

        // Decide whether this wedge counts against the loop guard. A wedge within
        // the re-wedge window of the last attempt is the loop signature; a wedge
        // after a long-healthy stretch is a fresh episode (attempts already reset
        // by the healthy branch above).
        let within_window = self.ticks_since_attempt <= self.policy.rewedge_window;
        if !within_window {
            // Fresh episode — make sure the budget is fresh.
            self.attempts = 0;
        }

        // If we've already exhausted the attempt budget, ESCALATE rather than
        // loop forever (the keystone restart-loop guard).
        if self.attempts >= self.policy.max_attempts {
            self.escalated = true;
            return Verdict::Escalate(Escalation::RecoveryNotHolding {
                attempts: self.attempts,
                last_artifact: artifact,
            });
        }

        // ACT: stop → restart → FRESH re-probe (fail-closed).
        self.subsystem.stop();
        self.subsystem.restart();
        self.attempts += 1;
        self.ticks_since_attempt = 0;

        // The FRESH probe is the only evidence of recovery we accept. We do NOT
        // trust restart()'s return, and we do NOT trust any post-restart claim.
        let fresh = self.subsystem.probe();
        if fresh.is_healthy() {
            return Verdict::Recovered {
                attempts: self.attempts,
            };
        }

        // The restart did NOT hold: the fresh probe still witnesses a wedge.
        // We NEVER claim success. If this just exhausted the budget, escalate;
        // otherwise report the caught divergence (if any) / the ongoing wedge so
        // the next tick re-attempts.
        let still = match fresh {
            ActualState::Wedged(r) => r,
            ActualState::Healthy => unreachable!(),
        };
        if self.attempts >= self.policy.max_attempts {
            self.escalated = true;
            return Verdict::Escalate(Escalation::RecoveryNotHolding {
                attempts: self.attempts,
                last_artifact: still,
            });
        }
        // Surface the structural catch when the subsystem had CLAIMED recovery;
        // otherwise report the ongoing (still-wedged) divergence so the loop is
        // visible. Either way the next tick re-attempts (fail-closed: never a
        // false "recovered").
        let _ = divergence_caught;
        Verdict::Diverged(Divergence::RecoveryNotHolding { artifact: still })
    }
}

// ───────────────────── recursive: a monitor IS a subsystem ───────────────────

/// Wrap a [`RecoveryMonitor`] so it can ITSELF be watched by another monitor —
/// the Houyhnhnm "virtualized monitors of monitors" (ch3, ch6). Its LIVE
/// ARTIFACT is its own escalation state (has it given up its charge?), read by
/// the parent the SAME way any artifact is read — never by trusting a claim. Its
/// "restart" is a [`RecoveryMonitor::reset`] + a re-tick (re-attempt the charge);
/// the parent then re-probes to see if the child monitor recovered its charge.
///
/// This is the keystone of recursion: a supervisory monitor can recover a
/// monitor that itself gave up, with the exact same probe/divergence/restart
/// machinery — turtles all the way up, each reading the layer below's ARTIFACT.
pub struct MonitorSubsystem<S: Subsystem> {
    inner: RecoveryMonitor<S>,
    label: String,
}

impl<S: Subsystem> MonitorSubsystem<S> {
    /// Wrap `inner` so a parent monitor can watch it under `label`.
    pub fn new(inner: RecoveryMonitor<S>, label: impl Into<String>) -> Self {
        MonitorSubsystem {
            inner,
            label: label.into(),
        }
    }

    /// Borrow the wrapped monitor (e.g. to drive its own ticks between parent
    /// ticks, or to inspect its charge).
    pub fn inner(&self) -> &RecoveryMonitor<S> {
        &self.inner
    }
    /// Mutably borrow the wrapped monitor.
    pub fn inner_mut(&mut self) -> &mut RecoveryMonitor<S> {
        &mut self.inner
    }
}

impl<S: Subsystem> Subsystem for MonitorSubsystem<S> {
    /// The child monitor's LIVE ARTIFACT: has it escalated (given up on its
    /// charge)? An escalated child is `Wedged`; a non-escalated child is
    /// `Healthy`. Read directly from the child's own state — never a claim.
    fn probe(&mut self) -> ActualState {
        if self.inner.has_escalated() {
            ActualState::Wedged(format!(
                "child monitor escalated after {} attempts on its charge",
                self.inner.attempts()
            ))
        } else {
            ActualState::Healthy
        }
    }

    /// A child monitor never lies UPWARD (it has no self-report channel of its
    /// own); the parent always reads the artifact. So the claim is `None`.
    fn claim(&self) -> Claim {
        Claim::None
    }

    /// Stopping a child monitor is a no-op at this layer (a monitor holds no OS
    /// resource of its own; its charge's lifecycle is the child's to drive).
    fn stop(&mut self) -> bool {
        true
    }

    /// "Restart" the child monitor: clear its escalation/attempt budget and
    /// re-attempt its charge once. The parent then RE-PROBES to see whether the
    /// child recovered its charge — fail-closed, exactly like any other restart.
    fn restart(&mut self) -> bool {
        self.inner.reset();
        // Re-drive the child once so a transient charge-wedge gets a fresh shot;
        // the parent's fresh probe is what decides whether it held.
        let _ = self.inner.tick();
        true
    }

    fn label(&self) -> &str {
        &self.label
    }
}

// ─────────────── the REAL host-PD adapter (the live Endpoint probe) ───────────

/// A [`Subsystem`] backed by a REAL confined host-PD whose live artifact is the
/// firmament Endpoint round-trip — the genuine "read the artifact, not the
/// claim" for the sandboxed firmament. Available under `process-pd` (Unix).
///
/// The probe invokes the host-PD capability through the [`crate::HostPdBacking`]
/// — the SAME validated Endpoint round-trip the router uses
/// ([`crate::HostPdBacking::invoke`] confirms the confined child's control socket
/// is LIVE; a closed Endpoint = the child is gone = wedged). It does NOT read any
/// log or self-report: holding-the-Endpoint-and-round-tripping-it IS the witness.
///
/// `stop`/`restart` are wired through the caller-supplied lifecycle closures
/// (the monitor stays decoupled from the concrete spawn machinery a sibling lane
/// may evolve; it depends only on the public `HostPdBacking` probe surface + two
/// lifecycle hooks). `restart` must re-register the fresh child's Endpoint into
/// the backing under the SAME [`crate::HostPdId`] so the next probe reaches the
/// new instance.
#[cfg(all(feature = "process-pd", unix))]
pub struct HostPdSubsystem<Stop, Restart>
where
    Stop: FnMut(&mut crate::HostPdBacking, crate::HostPdId) -> bool,
    Restart: FnMut(&mut crate::HostPdBacking, crate::HostPdId) -> bool,
{
    backing: crate::HostPdBacking,
    pd: crate::HostPdId,
    rights: crate::Rights,
    stop_fn: Stop,
    restart_fn: Restart,
    label: String,
}

#[cfg(all(feature = "process-pd", unix))]
impl<Stop, Restart> HostPdSubsystem<Stop, Restart>
where
    Stop: FnMut(&mut crate::HostPdBacking, crate::HostPdId) -> bool,
    Restart: FnMut(&mut crate::HostPdBacking, crate::HostPdId) -> bool,
{
    /// Watch host-PD `pd` (rights `rights`) registered in `backing`. `stop_fn` /
    /// `restart_fn` drive the PD lifecycle (terminate / re-spawn + re-register).
    pub fn new(
        backing: crate::HostPdBacking,
        pd: crate::HostPdId,
        rights: crate::Rights,
        stop_fn: Stop,
        restart_fn: Restart,
        label: impl Into<String>,
    ) -> Self {
        HostPdSubsystem {
            backing,
            pd,
            rights,
            stop_fn,
            restart_fn,
            label: label.into(),
        }
    }

    /// The backing (e.g. to re-probe directly).
    pub fn backing(&self) -> &crate::HostPdBacking {
        &self.backing
    }
}

#[cfg(all(feature = "process-pd", unix))]
impl<Stop, Restart> Subsystem for HostPdSubsystem<Stop, Restart>
where
    Stop: FnMut(&mut crate::HostPdBacking, crate::HostPdId) -> bool,
    Restart: FnMut(&mut crate::HostPdBacking, crate::HostPdId) -> bool,
{
    /// The LIVE ARTIFACT: invoke the host-PD capability — a validated Endpoint
    /// round-trip. A live, authorized Endpoint = `Healthy`; a closed Endpoint
    /// (child gone) or a rejected invocation = `Wedged`. This reaches the REAL
    /// confined child RIGHT NOW; there is no log to lie.
    fn probe(&mut self) -> ActualState {
        match self.backing.invoke(self.pd, &self.rights) {
            Ok(_resolution) => ActualState::Healthy,
            Err(e) => ActualState::Wedged(format!("host-PD {:?} Endpoint probe failed: {:?}", self.pd, e)),
        }
    }

    fn stop(&mut self) -> bool {
        (self.stop_fn)(&mut self.backing, self.pd)
    }

    fn restart(&mut self) -> bool {
        (self.restart_fn)(&mut self.backing, self.pd)
    }

    fn label(&self) -> &str {
        &self.label
    }
}

// ─────────────────────────────────── tests ──────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;
    use std::rc::Rc;

    /// A MOCK subsystem with INDEPENDENTLY controllable real-state vs claimed-
    /// state — so a test can simulate "logs OK but is actually wedged" (the
    /// exact 15-hour-wedge shape). The shared `Cell`-backed state lets a test
    /// drive the artifact AND the claim, and observe stop/restart calls.
    #[derive(Clone)]
    struct MockState {
        /// What the LIVE ARTIFACT witnesses (drive this independently of claim).
        actual: ActualState,
        /// What the subsystem CLAIMS (the self-report — may diverge from actual).
        claim: Claim,
        /// On restart, the state the artifact becomes — lets a test make a
        /// restart actually HOLD (-> Healthy) or keep re-wedging (-> Wedged).
        on_restart: ActualState,
        /// On restart, the claim the subsystem makes afterward (e.g. it keeps
        /// claiming `Recovered` even though the artifact re-wedged — the lie).
        on_restart_claim: Claim,
        stops: u32,
        restarts: u32,
    }

    #[derive(Clone)]
    struct Mock {
        st: Rc<RefCell<MockState>>,
    }

    impl Mock {
        fn new(actual: ActualState, claim: Claim) -> (Self, Rc<RefCell<MockState>>) {
            let st = Rc::new(RefCell::new(MockState {
                actual,
                claim,
                on_restart: ActualState::Healthy,
                on_restart_claim: Claim::None,
                stops: 0,
                restarts: 0,
            }));
            (Mock { st: st.clone() }, st)
        }
    }

    impl Subsystem for Mock {
        fn probe(&mut self) -> ActualState {
            // Reads the LIVE ARTIFACT — the `actual` field — NEVER the claim.
            self.st.borrow().actual.clone()
        }
        fn claim(&self) -> Claim {
            self.st.borrow().claim.clone()
        }
        fn stop(&mut self) -> bool {
            self.st.borrow_mut().stops += 1;
            true
        }
        fn restart(&mut self) -> bool {
            let mut s = self.st.borrow_mut();
            s.restarts += 1;
            // The restart drives the artifact + claim to their post-restart
            // values — the test controls whether it HOLDS or RE-WEDGES.
            s.actual = s.on_restart.clone();
            s.claim = s.on_restart_claim.clone();
            true
        }
        fn label(&self) -> &str {
            "mock"
        }
    }

    /// (a) A healthy subsystem → probe passes, NO action taken.
    #[test]
    fn healthy_subsystem_no_action() {
        let (m, st) = Mock::new(ActualState::Healthy, Claim::None);
        let mut mon = RecoveryMonitor::with_default_policy(m);
        assert_eq!(mon.tick(), Verdict::Healthy);
        // No stop/restart was ever called — the monitor does nothing to a healthy
        // thing. (Contrast a churn-loop that restarts a working system.)
        assert_eq!(st.borrow().stops, 0);
        assert_eq!(st.borrow().restarts, 0);
        assert!(!mon.has_escalated());
    }

    /// (b) THE KEYSTONE CATCH. A wedged subsystem that CLAIMS recovered →
    /// the monitor reads the ARTIFACT (wedged), ignores the claim (recovered),
    /// and — because the restart keeps re-wedging while still claiming OK —
    /// detects RecoveryNotHolding. This is the structural catch of
    /// assertion-over-artifact: `revert OK` over a live artifact that refutes it.
    #[test]
    fn claims_recovered_but_artifact_wedged_is_caught() {
        let (m, st) = Mock::new(ActualState::wedged("token dead"), Claim::Recovered);
        // The restart "succeeds" (and the subsystem keeps logging Recovered),
        // but the live artifact RE-WEDGES every time — the 15-hour-wedge shape.
        {
            let mut s = st.borrow_mut();
            s.on_restart = ActualState::wedged("token dead again (re-wedged)");
            s.on_restart_claim = Claim::Recovered; // it KEEPS claiming OK
        }
        let mut mon = RecoveryMonitor::with_default_policy(m);

        // First tick: artifact wedged, claim says Recovered → the monitor acts
        // (stop+restart), the fresh probe STILL witnesses a wedge → Diverged
        // RecoveryNotHolding (NOT a false Recovered — the claim was refuted).
        let v = mon.tick();
        match v {
            Verdict::Diverged(Divergence::RecoveryNotHolding { artifact }) => {
                assert!(artifact.contains("re-wedged"), "got artifact: {artifact}");
            }
            other => panic!("expected RecoveryNotHolding divergence, got {other:?}"),
        }
        // It DID act (it didn't just believe the log).
        assert_eq!(st.borrow().restarts, 1);
        // And on the NEXT tick it STILL refuses to claim recovery — the artifact
        // keeps refuting the `Recovered` claim, so it never reports Recovered.
        assert!(
            !matches!(mon.tick(), Verdict::Recovered { .. }),
            "monitor must NEVER claim recovery while the artifact refutes it"
        );
    }

    /// (c) A restart that ACTUALLY HOLDS → the monitor confirms via a FRESH
    /// probe and reports Recovered (witnessed, not claimed).
    #[test]
    fn restart_that_holds_is_recovered() {
        let (m, st) = Mock::new(ActualState::wedged("hung"), Claim::None);
        // The restart drives the artifact to Healthy — a recovery that holds.
        st.borrow_mut().on_restart = ActualState::Healthy;
        let mut mon = RecoveryMonitor::with_default_policy(m);

        let v = mon.tick();
        assert_eq!(v, Verdict::Recovered { attempts: 1 });
        assert_eq!(st.borrow().stops, 1);
        assert_eq!(st.borrow().restarts, 1);
        assert!(!mon.has_escalated());

        // A subsequent tick is steady-state Healthy (the fresh artifact holds).
        assert_eq!(mon.tick(), Verdict::Healthy);
    }

    /// (d) A re-wedge LOOP → the restart-loop counter escalates after N attempts
    /// instead of looping forever. The council's exact counter under fire.
    #[test]
    fn rewedge_loop_escalates_after_n() {
        let (m, st) = Mock::new(ActualState::wedged("wedge 0"), Claim::Recovered);
        // EVERY restart re-wedges immediately (within the window) — the loop.
        {
            let mut s = st.borrow_mut();
            s.on_restart = ActualState::wedged("re-wedged");
            s.on_restart_claim = Claim::Recovered;
        }
        let policy = MonitorPolicy {
            max_attempts: 3,
            rewedge_window: 4,
        };
        let mut mon = RecoveryMonitor::new(m, policy);

        // Ticks 1..=2 each attempt a recovery that re-wedges within the window →
        // Diverged, attempt counter climbing (budget not yet spent).
        for i in 1..=2 {
            let v = mon.tick();
            assert!(
                matches!(v, Verdict::Diverged(_)),
                "tick {i}: expected Diverged, got {v:?}"
            );
            assert_eq!(mon.attempts(), i);
        }
        // Tick 3 makes the 3rd attempt, the fresh probe STILL re-wedges, and the
        // budget is now spent (attempts == max_attempts == 3) → ESCALATE. The
        // monitor escalates the instant its budget is exhausted (fail-closed),
        // and does NOT keep restarting forever — the loop is STOPPED.
        let v = mon.tick();
        match v {
            Verdict::Escalate(Escalation::RecoveryNotHolding { attempts, .. }) => {
                assert_eq!(attempts, 3);
            }
            other => panic!("expected Escalate when budget spent, got {other:?}"),
        }
        assert!(mon.has_escalated());
        let restarts_after_escalate = st.borrow().restarts;
        assert_eq!(restarts_after_escalate, 3, "exactly 3 restarts, then it STOPS");

        // Further ticks attempt NO new restart — the loop is broken for good.
        let _ = mon.tick();
        assert_eq!(st.borrow().restarts, restarts_after_escalate);

        // Fail-closed: it STAYS escalated until a supervisory reset.
        assert!(matches!(mon.tick(), Verdict::Escalate(_)));

        // A supervisory reset re-arms it (the recursive parent's "restart").
        mon.reset();
        assert!(!mon.has_escalated());
        assert_eq!(mon.attempts(), 0);
    }

    /// A recovery that HOLDS past the re-wedge window FORGIVES the attempt
    /// counter — a later, unrelated wedge gets a fresh budget (no spurious
    /// escalation from accumulated, long-ago attempts).
    #[test]
    fn held_recovery_resets_the_loop_guard() {
        let (m, st) = Mock::new(ActualState::wedged("transient"), Claim::None);
        st.borrow_mut().on_restart = ActualState::Healthy;
        let policy = MonitorPolicy {
            max_attempts: 2,
            rewedge_window: 2,
        };
        let mut mon = RecoveryMonitor::new(m, policy);

        // One recovery that holds.
        assert_eq!(mon.tick(), Verdict::Recovered { attempts: 1 });
        assert_eq!(mon.attempts(), 1);
        // Stay healthy past the re-wedge window → the guard resets.
        for _ in 0..(policy.rewedge_window + 1) {
            assert_eq!(mon.tick(), Verdict::Healthy);
        }
        assert_eq!(mon.attempts(), 0, "held recovery should forgive the counter");
    }

    /// (e) RECURSIVE: a monitor watching a monitor. The inner monitor gives up
    /// on its charge (escalates); the OUTER monitor reads the inner's ARTIFACT
    /// (escalated == wedged), restarts it (reset + re-attempt), and — once the
    /// charge can recover — the outer monitor witnesses the inner healthy again.
    #[test]
    fn recursive_monitor_of_monitor() {
        // The inner charge: re-wedges at first, so the inner monitor escalates.
        let (charge, charge_st) = Mock::new(ActualState::wedged("charge down"), Claim::Recovered);
        {
            let mut s = charge_st.borrow_mut();
            s.on_restart = ActualState::wedged("charge still down");
            s.on_restart_claim = Claim::Recovered;
        }
        let inner_policy = MonitorPolicy {
            max_attempts: 2,
            rewedge_window: 4,
        };
        let mut inner = RecoveryMonitor::new(charge, inner_policy);
        // Drive the inner monitor until it gives up on its (un-fixable) charge.
        for _ in 0..5 {
            let _ = inner.tick();
        }
        assert!(inner.has_escalated(), "inner monitor should have escalated");

        // Now wrap the escalated inner monitor as a SUBSYSTEM and watch it with
        // an OUTER monitor. The outer reads the inner's ARTIFACT (escalated).
        let mut outer = RecoveryMonitor::with_default_policy(MonitorSubsystem::new(
            inner,
            "inner-monitor",
        ));

        // Before the outer acts, make the underlying CHARGE fixable, so that when
        // the outer "restarts" the inner (reset + re-tick), the inner's charge
        // recovers and the inner stops being escalated.
        charge_st.borrow_mut().on_restart = ActualState::Healthy;

        // The outer's first tick: probes the inner (wedged: escalated), acts
        // (reset+re-tick the inner → its charge now recovers), fresh-probes the
        // inner (no longer escalated) → Recovered. A monitor recovered a monitor.
        let v = outer.tick();
        assert_eq!(v, Verdict::Recovered { attempts: 1 });
        assert!(!outer.subsystem().inner().has_escalated());

        // Steady state: the inner monitor is healthy, so the outer is healthy.
        assert_eq!(outer.tick(), Verdict::Healthy);
    }

    /// A plain wedge with NO claim (the subsystem doesn't lie) that a restart
    /// fixes → Recovered. Confirms the monitor acts on the ARTIFACT alone, even
    /// with no claim to cross-check.
    #[test]
    fn wedge_without_claim_recovers_on_artifact_alone() {
        let (m, st) = Mock::new(ActualState::wedged("silent wedge"), Claim::None);
        st.borrow_mut().on_restart = ActualState::Healthy;
        let mut mon = RecoveryMonitor::with_default_policy(m);
        assert_eq!(mon.tick(), Verdict::Recovered { attempts: 1 });
        assert_eq!(st.borrow().restarts, 1);
    }
}
