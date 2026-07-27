/-
ProxyBreakerCorrect — correctness of the circuit breaker by refinement.

A circuit breaker guards an upstream with a three-state machine that fails fast
once the upstream looks dead and probes for recovery after a cooldown:

  * CLOSED    — traffic passes; consecutive failures are counted; reaching the
                `threshold`-th consecutive failure TRIPS the breaker OPEN.
  * OPEN      — every request is rejected fast; after the `cooldown` has elapsed
                (measured on the clock), the breaker moves to HALF-OPEN.
  * HALF-OPEN — a single trial probe is admitted; its SUCCESS closes the
                breaker, its FAILURE re-opens it, and while that probe is in
                flight further requests are rejected.

and a request reaches the upstream iff the breaker is CLOSED, or HALF-OPEN with
no trial probe already outstanding. This is the standard Circuit Breaker state
machine (Nygard, *Release It!* 2nd ed., ch. 5, "Circuit Breaker"; Fowler, "Circuit
Breaker", 2014), whose three phases and closed→open (threshold) / open→half-open
(timeout) / half-open→{closed,open} (probe result) transitions this module states
as an INDEPENDENT FSM (`specStep`, below) — written only from the prose above,
with no reference to the running machine `Proxy.Breaker.step` — and proves the
running machine refines it on every event history: the deployed breaker admits a
request EXACTLY when the specification does (`breaker_admits_refines_spec`), and
its phase tracks the specification's phase (`breaker_phase_refines_spec`).

The specification is deliberately NOT the implementation renamed:

  * its phase type `SPhase` is a DISTINCT type from the implementation's
    `Proxy.Breaker.BPhase`, coupled through `bphaseOf`, so the two machines
    cannot be literally the same term;
  * on a TRIP the specification KEEPS the running consecutive-failure count
    (`fails := st.fails + 1`), whereas the implementation zeroes its counter
    (`failures := 0`). The two counters therefore DIVERGE across the whole
    open / half-open stretch, re-converging only when a probe success returns
    the machine to closed. That divergence is invisible at the phase/admission
    boundary — outside closed nothing consults the counter — which is exactly
    why the refinement is an invariant argument (`rel_step`) and not a `rfl`.

Non-vacuity (`broken_admits_while_open_fails`, `broken_never_trips_fails`): a
breaker that admits a request while OPEN, or one that never trips, provably
DISAGREES with the specification on a concrete history — so the refinement has
genuine content and a wrong implementation fails it.
-/

import Proxy.Breaker

namespace Proxy.BreakerSpec

open Proxy.Breaker

/-! ## The independent specification

A breaker phase and the state the standard machine needs to decide its
transitions: the running consecutive-failure count, the clock instant the
breaker last opened (the cooldown origin), whether a half-open trial probe is
outstanding, and the latest observed clock. `SPhase` is a DISTINCT type from the
implementation's `BPhase`, so the specification cannot be the implementation
under another name. -/

/-- Specified breaker phase (independent of the implementation's `BPhase`). -/
inductive SPhase where
  | closed
  | opened
  | halfOpen
deriving DecidableEq, Repr

/-- Specification state. `fails` is the consecutive-failure count; `openedAt` is
the clock instant the breaker last opened; `probing` marks an outstanding
half-open trial; `clock` is the latest observed clock. -/
structure SpecState where
  phase : SPhase
  fails : Nat
  openedAt : Nat
  probing : Bool
  clock : Nat
deriving DecidableEq, Repr

/-- A fresh, closed breaker. -/
def SpecState.start : SpecState :=
  { phase := .closed, fails := 0, openedAt := 0, probing := false, clock := 0 }

/-- The specified transition, written straight from the Circuit Breaker rule.

* a `tick` advances the clock; while OPEN, once `cooldown` has elapsed since the
  breaker opened it moves to HALF-OPEN with no probe outstanding, otherwise it
  stays OPEN;
* a `probe` in HALF-OPEN marks the single trial outstanding (a second probe
  changes nothing while one is in flight); elsewhere it changes no state;
* a `success` clears the closed streak, and in HALF-OPEN closes the breaker;
* a `failure` in CLOSED extends the streak and, once it reaches `threshold`,
  TRIPS to OPEN (stamping the cooldown origin) — the count is KEPT, not zeroed;
  in HALF-OPEN a single failure re-opens the breaker. -/
def specStep (cfg : BreakerCfg) (st : SpecState) : BEvent → SpecState
  | .tick now =>
    let clk := max st.clock now
    match st.phase with
    | .opened =>
      if cfg.cooldown ≤ now - st.openedAt then
        { st with phase := .halfOpen, probing := false, clock := clk }
      else
        { st with clock := clk }
    | _ => { st with clock := clk }
  | .probe =>
    match st.phase with
    | .halfOpen => if st.probing then st else { st with probing := true }
    | _ => st
  | .success =>
    match st.phase with
    | .closed => { st with fails := 0 }
    | .opened => st
    | .halfOpen => { st with phase := .closed, fails := 0, probing := false }
  | .failure =>
    match st.phase with
    | .closed =>
      if cfg.threshold ≤ st.fails + 1 then
        { st with phase := .opened, fails := st.fails + 1, openedAt := st.clock }
      else
        { st with fails := st.fails + 1 }
    | .opened => st
    | .halfOpen => { st with phase := .opened, probing := false, openedAt := st.clock }

/-- Run an event history through the specification, oldest first. -/
def specRun (cfg : BreakerCfg) (st : SpecState) : List BEvent → SpecState
  | [] => st
  | e :: es => specRun cfg (specStep cfg st e) es

/-- Specified admission: a request reaches the upstream iff the breaker is
CLOSED, or HALF-OPEN with no trial probe already outstanding. -/
def SpecState.admits (st : SpecState) : Bool :=
  match st.phase with
  | .closed => true
  | .opened => false
  | .halfOpen => !st.probing

@[simp] theorem specRun_cons (cfg : BreakerCfg) (st : SpecState) (e : BEvent)
    (es : List BEvent) :
    specRun cfg st (e :: es) = specRun cfg (specStep cfg st e) es := rfl

/-! ## The refinement invariant

The implementation `Proxy.Breaker.step` / `Proxy.Breaker.run` refines the
specification: the phases correspond, the probe-in-flight flag, cooldown origin,
and clock always agree, and the failure counters agree while closed. -/

/-- The specified phase, viewed as an implementation phase. -/
def bphaseOf : SPhase → BPhase
  | .closed => .closed
  | .opened => .open
  | .halfOpen => .halfOpen

/-- The coupling invariant between an implementation state and a spec state. -/
structure Rel (s : BState) (st : SpecState) : Prop where
  phase : s.phase = bphaseOf st.phase
  probing : s.probeInFlight = st.probing
  openedAt : s.openedAt = st.openedAt
  clock : s.clock = st.clock
  failsClosed : s.phase = .closed → s.failures = st.fails

/-- The aligned start states are related. -/
theorem rel_start : Rel BState.init SpecState.start where
  phase := rfl
  probing := rfl
  openedAt := rfl
  clock := rfl
  failsClosed := fun _ => rfl

/-- **One-step refinement.** `Rel` is preserved by any event. This holds despite
the two machines disagreeing on the failure counter across the open / half-open
stretch (the trip keeps the count in the spec, zeroes it in the impl). -/
theorem rel_step (cfg : BreakerCfg) (s : BState) (st : SpecState)
    (h : Rel s st) (e : BEvent) :
    Rel (step cfg s e).1 (specStep cfg st e) := by
  obtain ⟨sph, sf, so, spr, scl⟩ := s
  obtain ⟨tph, tf, to, tpr, tcl⟩ := st
  obtain ⟨hp, hpr, ho, hc, hf⟩ := h
  simp only at hp hpr ho hc hf
  subst hpr; subst ho; subst hc
  cases tph with
  | closed =>
    subst hp
    have hsf : sf = tf := hf rfl
    subst hsf
    cases e with
    | tick now =>
      refine ⟨rfl, rfl, rfl, rfl, ?_⟩; intro _; rfl
    | probe =>
      refine ⟨rfl, rfl, rfl, rfl, ?_⟩; intro _; rfl
    | success =>
      refine ⟨rfl, rfl, rfl, rfl, ?_⟩; intro _; rfl
    | failure =>
      simp only [step, specStep, bphaseOf]
      by_cases hthr : cfg.threshold ≤ sf + 1
      · rw [if_pos hthr, if_pos hthr]
        exact ⟨rfl, rfl, rfl, rfl, by simp⟩
      · rw [if_neg hthr, if_neg hthr]
        exact ⟨rfl, rfl, rfl, rfl, by intro _; rfl⟩
  | opened =>
    subst hp
    cases e with
    | tick now =>
      simp only [step, specStep, bphaseOf]
      by_cases hcd : cfg.cooldown ≤ now - so
      · rw [if_pos hcd, if_pos hcd]
        exact ⟨rfl, rfl, rfl, rfl, by simp⟩
      · rw [if_neg hcd, if_neg hcd]
        exact ⟨rfl, rfl, rfl, rfl, by simp⟩
    | probe =>
      refine ⟨rfl, rfl, rfl, rfl, ?_⟩
      simp [step, specStep, bphaseOf]
    | success =>
      refine ⟨rfl, rfl, rfl, rfl, ?_⟩
      simp [step, specStep, bphaseOf]
    | failure =>
      refine ⟨rfl, rfl, rfl, rfl, ?_⟩
      simp [step, specStep, bphaseOf]
  | halfOpen =>
    subst hp
    cases e with
    | tick now =>
      refine ⟨rfl, rfl, rfl, rfl, ?_⟩
      simp [step, specStep, bphaseOf]
    | probe =>
      cases spr with
      | true =>
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
          simp [step, specStep, bphaseOf]
      | false =>
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
          simp [step, specStep, bphaseOf]
    | success =>
      refine ⟨rfl, rfl, rfl, rfl, ?_⟩; intro _; rfl
    | failure =>
      refine ⟨rfl, rfl, rfl, rfl, ?_⟩
      simp [step, specStep, bphaseOf]

/-- `Rel` is preserved across a whole event history. -/
theorem rel_run (cfg : BreakerCfg) (s : BState) (st : SpecState)
    (h : Rel s st) : (trace : List BEvent) →
    Rel (run cfg s trace) (specRun cfg st trace)
  | [] => by simpa using h
  | e :: es => by
    rw [run_cons, specRun_cons]
    exact rel_run cfg (step cfg s e).1 (specStep cfg st e) (rel_step cfg s st h e) es

/-- `Rel` forces the admission verdicts to coincide: the deployed breaker's
probe output matches the specified admission decision. -/
theorem rel_admits {s : BState} {st : SpecState} (h : Rel s st)
    (cfg : BreakerCfg) :
    (step cfg s .probe).2
      = (if st.admits then [BOutput.attempt] else [BOutput.reject]) := by
  have hp := h.phase
  have hpr := h.probing
  cases htp : st.phase with
  | closed =>
    have : s.phase = .closed := by rw [hp, htp]; rfl
    simp [step, this, SpecState.admits, htp]
  | opened =>
    have : s.phase = .open := by rw [hp, htp]; rfl
    simp [step, this, SpecState.admits, htp]
  | halfOpen =>
    have hph : s.phase = .halfOpen := by rw [hp, htp]; rfl
    simp only [step, hph, SpecState.admits, htp]
    cases hpb : st.probing with
    | true =>
      have : s.probeInFlight = true := by rw [hpr, hpb]
      simp [this]
    | false =>
      have : s.probeInFlight = false := by rw [hpr, hpb]
      simp [this]

/-! ## The refinement theorems -/

/-- **CORRECTNESS OF CIRCUIT-BREAKER ADMISSION.** For every configuration and
every event history, the deployed breaker admits a request onto the upstream
(`step … .probe` emits `attempt`) EXACTLY when the independent specification
does. The breaker fails fast iff the specified machine is OPEN, or HALF-OPEN
with a probe already outstanding. -/
theorem breaker_admits_refines_spec (cfg : BreakerCfg) (trace : List BEvent) :
    (step cfg (run cfg BState.init trace) .probe).2
      = (if (specRun cfg SpecState.start trace).admits
          then [BOutput.attempt] else [BOutput.reject]) :=
  rel_admits (rel_run cfg BState.init SpecState.start rel_start trace) cfg

/-- **CORRECTNESS OF CIRCUIT-BREAKER STATE.** For every configuration and every
event history, the deployed breaker's phase corresponds to the independently
specified phase. Together with admission this pins the breaker to the standard
closed/open/half-open machine on all inputs. -/
theorem breaker_phase_refines_spec (cfg : BreakerCfg) (trace : List BEvent) :
    (run cfg BState.init trace).phase
      = bphaseOf (specRun cfg SpecState.start trace).phase :=
  (rel_run cfg BState.init SpecState.start rel_start trace).phase

/-! ## Non-vacuity: wrong breakers fail the specification

Two broken breakers a proxy must NOT ship. Each provably disagrees with the
specification on a concrete history, so the refinement theorems above have
genuine content — they are not `spec = spec`. -/

/-- Broken breaker A: ADMITS WHILE OPEN — answers every probe with `attempt`,
even when the circuit is open. -/
def badAdmitStep (cfg : BreakerCfg) (s : BState) : BEvent → BState × List BOutput
  | .probe => (s, [BOutput.attempt])
  | e => step cfg s e

/-- With `threshold = 2`, two consecutive failures open the breaker; the
specification then rejects a probe fast, yet the admit-while-open breaker emits
`attempt`. They disagree, so admitting while open is not a valid breaker. -/
theorem broken_admits_while_open_fails :
    (badAdmitStep ⟨2, 5⟩ (run ⟨2, 5⟩ BState.init [.failure, .failure]) .probe).2
      ≠ (if (specRun ⟨2, 5⟩ SpecState.start [.failure, .failure]).admits
          then [BOutput.attempt] else [BOutput.reject]) := by
  decide

/-- Broken breaker B: NEVER TRIPS — a closed-side failure only ever increments
the counter, so the circuit never opens. -/
def noTripStep (cfg : BreakerCfg) (s : BState) : BEvent → BState × List BOutput
  | .failure =>
    match s.phase with
    | .closed => ({ s with failures := s.failures + 1 }, [])
    | _ => step cfg s .failure
  | e => step cfg s e

def noTripRun (cfg : BreakerCfg) (s : BState) : List BEvent → BState
  | [] => s
  | e :: es => noTripRun cfg (noTripStep cfg s e).1 es

/-- With `threshold = 2`, two consecutive failures must open the breaker (the
specification's phase is OPEN), yet the never-trips breaker stays CLOSED. They
disagree, so a breaker that never trips is not a valid breaker. -/
theorem broken_never_trips_fails :
    (noTripRun ⟨2, 5⟩ BState.init [.failure, .failure]).phase
      ≠ bphaseOf (specRun ⟨2, 5⟩ SpecState.start [.failure, .failure]).phase := by
  decide

/-- Sanity: the SPECIFICATION itself exhibits the behavior it claims. Two
failures at `threshold = 2` trip it open; before `cooldown = 5` a tick keeps it
open, at the cooldown a tick moves it to half-open; a half-open probe is
admitted, a success then closes it; a half-open failure re-opens it. (Concrete
`decide` checks of the spec, not the impl — the refinement theorems tie the impl
to it.) -/
example : (specRun ⟨2, 5⟩ SpecState.start [.failure]).phase = .closed := by decide
example : (specRun ⟨2, 5⟩ SpecState.start [.failure, .failure]).phase = .opened := by
  decide
example :
    (specRun ⟨2, 5⟩ SpecState.start [.failure, .failure, .tick 4]).phase = .opened := by
  decide
example :
    (specRun ⟨2, 5⟩ SpecState.start [.failure, .failure, .tick 5]).phase = .halfOpen := by
  decide
example :
    (specRun ⟨2, 5⟩ SpecState.start [.failure, .failure, .tick 5]).admits = true := by
  decide
example :
    (specRun ⟨2, 5⟩ SpecState.start
      [.failure, .failure, .tick 5, .probe, .success]).phase = .closed := by decide
example :
    (specRun ⟨2, 5⟩ SpecState.start
      [.failure, .failure, .tick 5, .probe, .failure]).phase = .opened := by decide

end Proxy.BreakerSpec
