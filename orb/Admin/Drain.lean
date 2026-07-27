/-
Admin.Drain — the proven monotonicity decision behind `POST /admin/drain`.

`POST /admin/drain` begins a STANDING graceful drain: the untrusted shell
(`reconfig::begin_drain`) sets a monotone flag (`DRAIN_BEGUN`, an idempotent
`swap(true)`) so `/healthz` flips to 503 (a fronting balancer bleeds new traffic
away) while every in-flight request finishes under its own config. This is the
whole-host application of the `beginDrain` event the proven drain FSM
(`Drain.step` / `DrainCorrect`) already models per config generation.

This file proves the two properties the admin drain relies on, composing the
proven FSM rather than re-deriving it:

  * `drain_monotone` — once the run has left the running mode (the drain window
    has begun), EVERY extension of the event history is still not-running: the
    drain is monotone, it never spontaneously re-opens for new work until a
    reload/restart resets the lifecycle. This is the FSM face of the monotone
    `DRAIN_BEGUN` flag;
  * `drain_no_admit_ext` — consequently, every accept attempt anywhere in the
    drained tail is refused (no new connection admitted while draining).

Both are lifted over history extension via a `run_append` glue lemma and the
proven `Drain.Trace.run_notRunning` / `acceptReq_refused_of_not_running`.
Non-vacuity: a concrete drained-then-extended run is still refusing accepts
(`by decide`), and a mutant flag that clears on any event is proved to VIOLATE
monotonicity.
-/

import Drain.Trace

namespace Admin
namespace Drain

open _root_.Drain (DState Event Output run step init acceptReq_refused_of_not_running
  run_notRunning)

/-! ## Glue: a run over a concatenated history is the run of the tail from the
head's end state. -/

/-- `run` distributes over history concatenation. -/
theorem run_append (s : DState) (es fs : List Event) :
    run s (es ++ fs) = run (run s es) fs := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih => simp only [List.cons_append, _root_.Drain.run_cons]; exact ih _

/-! ## Monotonicity of the drain window -/

/-- **Drain is monotone.** Once an event history `es` has driven the lifecycle out
of the running (accepting) mode — the drain window has begun — appending ANY
further history `fs` leaves it out of running. The drain never re-opens the
listener for new work on its own; only a reload/restart (a fresh `init`
lifecycle) returns to running. This is the proven-FSM face of the monotone
`DRAIN_BEGUN` flag the admin shell sets. -/
theorem drain_monotone (es fs : List Event) (h : (run init es).mode ≠ .running) :
    (run init (es ++ fs)).mode ≠ .running := by
  rw [run_append]; exact run_notRunning fs h

/-- **No new admit while draining.** In the drained tail (any extension of a
history that has left running), every accept attempt is refused — no new
connection is admitted while the host is draining. -/
theorem drain_no_admit_ext (es fs : List Event) (h : (run init es).mode ≠ .running) :
    (step (run init (es ++ fs)) .acceptReq).2 = [Output.refused] :=
  acceptReq_refused_of_not_running (drain_monotone es fs h)

/-- A single `beginDrain` event leaves the running mode, so it opens the drain
window that `drain_monotone` then holds across every extension. -/
theorem beginDrain_opens_window (dl : Nat) :
    (run init [Event.beginDrain dl]).mode ≠ .running := by
  rw [_root_.Drain.run_cons, _root_.Drain.run_nil]
  simp [step, init]

/-! ## Non-vacuity — a concrete drained tail, and a mutant that violates
monotonicity -/

/-- Concretely: accept one connection, begin draining, then no matter what
follows (here a further accept), the next accept is still refused. -/
example :
    (step (run init ([Event.acceptReq, Event.beginDrain 5] ++ [Event.acceptReq]))
       Event.acceptReq).2 = [Output.refused] := by decide

/-- The drain window, once open, is still open after an arbitrary concrete tail. -/
example : (run init ([Event.beginDrain 5] ++ [Event.acceptReq, Event.complete])).mode
    ≠ .running := by decide

/-! ### The monotone admin flag, and a mutant

The admin shell's `DRAIN_BEGUN` is a boolean that only ever goes false→true (an
idempotent `swap(true)`). We model that flag and prove its monotonicity, then a
mutant that clears the flag on a stray event and show it breaks monotonicity —
the exact failure mode (`/healthz` flipping back to 200 mid-drain, re-admitting
traffic) the real idempotent swap forbids. -/

/-- The admin drain flag folded over a sequence of "drain begun?" signals: once
set it stays set (`b || _` is monotone). -/
def flagRun (start : Bool) (signals : List Bool) : Bool :=
  signals.foldl (fun b s => b || s) start

/-- **The flag is monotone.** Once the drain flag is set, no sequence of further
signals clears it. -/
theorem flagRun_monotone (signals : List Bool) : flagRun true signals = true := by
  unfold flagRun
  induction signals with
  | nil => rfl
  | cons s ss ih => simpa using ih

/-- A mutant flag that RESETS to false on a `false` signal (a spurious event
clearing the drain) rather than latching. -/
def brokenFlagRun (start : Bool) (signals : List Bool) : Bool :=
  signals.foldl (fun _ s => s) start

/-- **Non-vacuity.** The resetting mutant breaks monotonicity: from a set flag a
single `false` signal clears it, so the latched-drain guarantee genuinely
depends on the monotone fold — the monotonicity theorem is not vacuous. -/
theorem brokenFlagRun_violates : brokenFlagRun true [false] = false := by decide

end Drain
end Admin
