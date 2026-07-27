/-
# DrainLive — driving the PROVEN graceful-drain FSM over the byte level

`POST /admin/drain` on the operator listener begins a STANDING graceful drain.
The untrusted shell (`reconfig::begin_drain`) sets a monotone flag
(`DRAIN_BEGUN`, an idempotent `swap(true)`); thereafter `/healthz` advertises
`503 draining` (a fronting balancer bleeds new traffic away) while every request
already in flight finishes under the config it started on, and no new connection
is admitted. The proven `Drain` foundation (`Drain.Basic` / `Drain.Trace`) models
that lifecycle as a transition system:

    running   — accepting; `/healthz` → 200 ok
    draining  — begin-drain fired: no new admit, in-flight complete
    drained   — every in-flight request finished (in-flight = 0)
    closed    — listener released (absorbing)

None of that DECISION was wired into a running binary at the byte level here.
This executable is that wiring: a `selftest` that drives the proven `step` / `run`
over a whole drain trace in one process — accept two connections, begin the
drain, watch the health projection flip to 503, watch a fresh accept get REFUSED,
let the two in-flight requests `complete` (reaching `drained`), then `tick` to
`closed` — and cross-checks every observable against the proven lemmas. It runs
under `lake env lean --run`: there is NO crypto and NO FFI on this path (the
drain lifecycle is pure structural logic — the admin drain lever is not on the
data plane).

## What is proven here (composing the proven FSM, not re-deriving it)

  * `beginDrain_leaves_running` — a `beginDrain` event, from ANY mode, lands in a
    non-running mode (running→draining/drained; the rest stutter, already
    non-running). This is the FSM face of the monotone `DRAIN_BEGUN` swap in
    `reconfig::begin_drain`;
  * `drain_refuses_new` — after a `beginDrain`, no matter what history follows,
    an accept attempt is `refused`: no new connection is admitted while draining
    (the `noAdmitAfterSignal` obligation, over the reachable trace);
  * `drain_completes_inflight` — a reachable running server with one request in
    flight, on `beginDrain` then `complete`, reaches `drained` with in-flight
    zero: the in-flight request FINISHES and only then is the lifecycle done
    (progress; nothing cut off mid-flight);
  * `health_not_ready_while_draining` — the byte-level `/healthz` projection
    (`healthStatus` / `healthBody`, mirroring `admin.rs`'s `serving()`) is
    EXACTLY `503` / `b"draining\n"` at every point of the drained tail;
  * `health_ready_when_running` — and EXACTLY `200` / `b"ok\n"` while running.

## Honesty / realization boundary

This is **drorb-native** and **pure**: `DrainLive.selftest` drives the proven
`Drain.step` / `Drain.run` directly — it is a rung-2 selftest, NOT the deployed
serve path. The realization gap the selftest discharges by construction (not by
proof) is that the running admin shell (`admin.rs` / `reconfig.rs`) CALLS this
decision faithfully: `/healthz` reads `serving()` and `POST /admin/drain` calls
`begin_drain()`. The health projection here is byte-identical to `admin.rs`
(`200 "ok\n"` vs `503 "draining\n"`), and `begin_drain`'s idempotent
`DRAIN_BEGUN.swap(true)` is the monotone `beginDrain` event modelled below. What
is proven is the DECISION and its byte-level health observable; the wiring is the
named residual, exactly as in NetmapLive / ControlLive.

Usage:
  drain-live selftest
-/
import Drain.Trace

namespace DrainLive

open Drain

/-! ## §1  The byte-level `/healthz` projection (mirrors `admin.rs::serving`)

`admin.rs` answers `GET /healthz` with `200 "ok\n"` while `serving()` (running,
no drain begun) and `503 "draining\n"` otherwise. We project the proven FSM state
to exactly those bytes: readiness is `mode = running`. -/

/-- The `/healthz` status code for a lifecycle state: `200` while accepting,
`503` once out of running (draining/drained/closed). Mirrors `admin.rs`. -/
def healthStatus (s : DState) : Nat :=
  if s.mode = Mode.running then 200 else 503

/-- The `/healthz` body bytes: `b"ok\n"` while accepting, `b"draining\n"` once a
drain has begun. Byte-identical to `admin.rs`. -/
def healthBody (s : DState) : ByteArray :=
  if s.mode = Mode.running then "ok\n".toUTF8 else "draining\n".toUTF8

/-- `true` iff the host advertises readiness (`/healthz` → 200). -/
def ready (s : DState) : Bool := s.mode = Mode.running

/-! ## §2  Drain begins → the run leaves running (monotone `DRAIN_BEGUN`) -/

/-- **Begin-drain leaves running.** A `beginDrain` event, applied from ANY mode,
lands in a non-running mode: from running it goes to draining (work in flight) or
straight to drained (idle); draining/drained/closed already stutter out of
running. This is the FSM face of the monotone `DRAIN_BEGUN.swap(true)` in
`reconfig::begin_drain` — once set, readiness is never re-advertised. -/
theorem beginDrain_leaves_running (s : DState) (dl : Nat) :
    (step s (Event.beginDrain dl)).1.mode ≠ Mode.running := by
  simp only [step]
  split
  · split <;> simp
  · rename_i h; simp [h]
  · rename_i h; simp [h]
  · rename_i h; simp [h]

/-! ## §3  No new admit while draining -/

/-- **No new connection admitted once draining.** From any reachable state, once
a `beginDrain` has fired, an accept attempt after ANY further history `fs` is
`refused`. This is the trace form of the `noAdmitAfterSignal` obligation
(`reconfig.rs`): after the swap no new work is served under the drained host. -/
theorem drain_refuses_new (es fs : List Event) (dl : Nat) :
    (step (run (step (run init es) (Event.beginDrain dl)).1 fs) Event.acceptReq).2
      = [Output.refused] :=
  acceptReq_refused_of_not_running
    (run_notRunning fs (beginDrain_leaves_running (run init es) dl))

/-! ## §4  In-flight requests finish (progress), then the lifecycle drains

`run` distributes over history concatenation (local glue), so we can extend any
reachable running-with-one-in-flight history by `beginDrain, complete` and land
in `drained`. -/

/-- `run` distributes over history concatenation. -/
theorem run_append (s : DState) (es fs : List Event) :
    run s (es ++ fs) = run (run s es) fs := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih => simp only [List.cons_append, run_cons]; exact ih _

/-- **In-flight completes, then drains.** A reachable server still running with
exactly one request in flight, driven by `beginDrain dl` then `complete`, reaches
`drained` with in-flight zero. The in-flight request is NOT cut off: it finishes
(the `complete`), and only its completion — emptying the in-flight set — retires
the lifecycle. This composes the proven `complete_reaches_drained`. -/
theorem drain_completes_inflight (es : List Event) (dl : Nat)
    (hr : (run init es).mode = Mode.running) (hf : (run init es).inflight = 1) :
    (run init (es ++ [Event.beginDrain dl, Event.complete])).mode = Mode.drained
      ∧ (run init (es ++ [Event.beginDrain dl, Event.complete])).inflight = 0 := by
  rw [run_append]
  simp only [run_cons, run_nil]
  have hbd : step (run init es) (Event.beginDrain dl)
      = ({ run init es with mode := Mode.draining, deadline := dl }, []) := by
    simp only [step, hr]; rw [if_pos (by omega)]
  rw [hbd]
  exact complete_reaches_drained rfl hf

/-! ## §5  The health projection is faithful to the drain (byte level)

The faithfulness theorems: the byte-level `/healthz` observable is EXACTLY what
the FSM mode dictates. Once a drain has begun, every point of the drained tail
reads `503 "draining\n"`; while running it reads `200 "ok\n"`. This is the proven
tie between `admin.rs`'s `serving()` and the drain lifecycle. -/

/-- **Not ready while draining.** After a `beginDrain`, at every point of the
drained tail the byte-level `/healthz` projection is exactly `503` with body
`b"draining\n"` — the host stops advertising readiness for the whole drain, so a
fronting balancer bleeds new traffic away. -/
theorem health_not_ready_while_draining (s : DState) (fs : List Event) (dl : Nat) :
    healthStatus (run (step s (Event.beginDrain dl)).1 fs) = 503
      ∧ healthBody (run (step s (Event.beginDrain dl)).1 fs) = "draining\n".toUTF8
      ∧ ready (run (step s (Event.beginDrain dl)).1 fs) = false := by
  have h : (run (step s (Event.beginDrain dl)).1 fs).mode ≠ Mode.running :=
    run_notRunning fs (beginDrain_leaves_running s dl)
  refine ⟨?_, ?_, ?_⟩
  · simp only [healthStatus, if_neg h]
  · simp only [healthBody, if_neg h]
  · simp only [ready, decide_eq_false_iff_not]; exact h

/-- **Ready while running.** A running server advertises `200 "ok\n"`. -/
theorem health_ready_when_running (s : DState) (h : s.mode = Mode.running) :
    healthStatus s = 200 ∧ healthBody s = "ok\n".toUTF8 ∧ ready s = true := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [healthStatus, if_pos h]
  · simp only [healthBody, if_pos h]
  · simp only [ready, h]; rfl

/-! ## §6  Non-vacuity — a concrete full drain trace, and a mutant

The theorems above carry real hypotheses (an arbitrary reachable history, an
arbitrary drained tail). Here we pin a concrete trace so the guarantees are
visibly inhabited, and show a MUTANT health projection (ready whenever not
closed — the "drain still advertises 200" bug the real `serving()` forbids) that
breaks not-ready-while-draining. -/

/-- Concrete: accept two, begin drain, a fresh accept is refused. -/
example :
    (step (run init [Event.acceptReq, Event.acceptReq, Event.beginDrain 5])
      Event.acceptReq).2 = [Output.refused] := by decide

/-- Concrete happy drain: accept, begin, complete → drained; a tick → closed. -/
example :
    (run init [Event.acceptReq, Event.beginDrain 5, Event.complete, Event.tick 3]).mode
      = Mode.closed := by decide

/-- Concrete health flip: 200 while running, 503 the instant drain begins. -/
example : healthStatus (run init [Event.acceptReq]) = 200 := by decide
example : healthStatus (run init [Event.acceptReq, Event.beginDrain 5]) = 503 := by decide

/-- A MUTANT `/healthz` that stays ready until fully closed (advertising 200
mid-drain). It re-admits traffic during the drain window — exactly the failure
`admin.rs`'s `serving()` (false the instant `drain_begun()`) rules out. -/
def brokenHealthStatus (s : DState) : Nat :=
  if s.mode = Mode.closed then 503 else 200

/-- **Non-vacuity.** In a genuine draining state the mutant reads 200 (ready)
whereas the faithful `healthStatus` reads 503 — so `health_not_ready_while_draining`
genuinely depends on the `mode = running` readiness predicate, not a tautology. -/
theorem brokenHealthStatus_violates :
    let s := run init [Event.acceptReq, Event.beginDrain 5]
    brokenHealthStatus s = 200 ∧ healthStatus s = 503 := by decide

/-! ## §7  The selftest — the whole drain, byte level, one process, NO crypto -/

private def modeStr : Mode → String
  | .running => "running"
  | .draining => "draining"
  | .drained => "drained"
  | .closed => "closed"

private def bodyText (b : ByteArray) : String := (String.fromUTF8? b).getD "?"

/-- Print the observable admin state: mode, in-flight, and the byte-level
`/healthz` code + body — exactly what `admin.rs` would answer. -/
private def showHealth (label : String) (s : DState) : IO Unit :=
  IO.println s!"{label}  mode={modeStr s.mode}  inflight={s.inflight}  \
    /healthz -> {healthStatus s} {bodyText (healthBody s)|>.trim}  ready={ready s}"

def selftest : IO UInt32 := do
  IO.println "== drain-live selftest : graceful drain FSM, byte-level /healthz, NO crypto =="

  -- ── running: two connections accepted ───────────────────────────────────
  let s0 := init
  showHealth "boot        :" s0
  let s1 := (step s0 Event.acceptReq).1   -- admit conn #1
  let s2 := (step s1 Event.acceptReq).1   -- admit conn #2
  showHealth "2 accepted  :" s2
  let readyBefore := ready s2
  IO.println s!"admits before drain (both connections in flight) : inflight={s2.inflight}"

  -- ── POST /admin/drain : begin the standing graceful drain ────────────────
  IO.println "\n-- POST /admin/drain (beginDrain, deadline=5) --"
  let sD := (step s2 (Event.beginDrain 5)).1
  showHealth "draining    :" sD
  let healthFlipped := (healthStatus sD == 503) && (bodyText (healthBody sD) == "draining\n")
  IO.println s!"/healthz flipped to 503 draining : {healthFlipped}"

  -- ── a fresh accept is now REFUSED (no new admit while draining) ──────────
  let (sR, outR) := step sD Event.acceptReq
  let refusedNew := outR == [Output.refused]
  IO.println s!"fresh accept during drain refused : {refusedNew}  (output={repr outR})"
  IO.println s!"in-flight unchanged by refusal     : {sR.inflight == sD.inflight}"

  -- ── in-flight requests COMPLETE (not cut off), then the lifecycle drains ─
  IO.println "\n-- in-flight requests finish under their own config --"
  let s3 := (step sR Event.complete).1   -- conn #1 finishes  (2 -> 1, still draining)
  showHealth "1 completed :" s3
  let stillDraining := s3.mode == Mode.draining
  let s4 := (step s3 Event.complete).1   -- conn #2 finishes  (1 -> 0, -> drained)
  showHealth "2 completed :" s4
  let reachedDrained := (s4.mode == Mode.drained) && (s4.inflight == 0)
  IO.println s!"stayed draining while work outstanding : {stillDraining}"
  IO.println s!"reached drained once in-flight hit 0   : {reachedDrained}"

  -- ── tick closes the drained server ──────────────────────────────────────
  let s5 := (step s4 (Event.tick 9)).1
  showHealth "closed      :" s5
  let closed := s5.mode == Mode.closed

  -- ── accounting identity: nothing silently lost ──────────────────────────
  let accounted := s4.entered == s4.inflight + s4.completed + s4.forcedClosed
  IO.println s!"\naccounting identity (entered = inflight+completed+forcedClosed) : {accounted}  \
    (entered={s4.entered} completed={s4.completed})"

  -- ── cross-check every observable against the proven lemmas ──────────────
  IO.println "\n-- cross-check (realizes the proven Drain lemmas) --"
  IO.println s!"ready while running (health_ready_when_running)      : {readyBefore}"
  IO.println s!"not-ready while draining (health_not_ready_...)       : {!ready sD}"
  IO.println s!"drain refuses new (drain_refuses_new)                 : {refusedNew}"
  IO.println s!"in-flight completes then drains (drain_completes_...) : {reachedDrained}"
  IO.println s!"drained closes on tick (closed_absorbing)            : {closed}"

  let allPass := readyBefore && healthFlipped && refusedNew && stillDraining
    && reachedDrained && closed && accounted
  if allPass then do
    IO.println "\nPASS — drain begun: /healthz flipped to 503, new connections refused,"
    IO.println "       in-flight requests finished, lifecycle drained then closed; every"
    IO.println "       byte-level observable equals the proven Drain decision."
    IO.println "DRAIN LIVE-WIRED (drorb-native, byte-level /healthz, NO crypto, verified FSM)."
    return 0
  else do
    IO.eprintln "FAIL — a drain observable diverged from the proven model"
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["selftest"] => selftest
  | _ => do
    IO.eprintln "usage: drain-live selftest"
    return 1

end DrainLive

def main (args : List String) : IO UInt32 := DrainLive.main args
