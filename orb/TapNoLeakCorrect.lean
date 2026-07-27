/-
TapNoLeakCorrect — a standard-derived specification of the gated diagnostic
tap, and a refinement proof that the deployed `Tap.run` fold matches it on
every input.

The specification below is written from the operational contract of an
administratively-gated monitoring session, as standardised for switched-network
port copy in RFC 2613 (Remote Network Monitoring MIB Extensions for Switched
Networks — SMON), §"The portCopy Group".  A `portCopyEntry` copies traffic from
its source to its destination ONLY while the row's `portCopyStatus` is
`active(1)`; an absent or non-active row copies nothing, and while active a row
copies exactly its configured source and nothing else.  Translating that MIB
row lifecycle into a trace of control edges (`.enable` = row goes `active`,
`.disable` = row leaves `active`) and offered packets, the normative behaviour
is:

  * a packet is copied to the diagnostic destination IFF the copy session was
    `active` at the moment that packet was offered — i.e. the most recent
    control edge preceding it was `.enable` (or, absent any edge, the session
    started active);
  * an inactive session copies NOTHING (strong non-leak);
  * an active session with no intervening `.disable` copies EXACTLY the offered
    packets, in order.

The spec is defined WITHOUT reference to `Tap.step`, `Tap.run`, `Tap.tappedFrom`,
`Tap.gateAfter`, or `Tap.pktsOf`.  It is a two-pass reading of the trace:
`annotate` labels each event with the session state IN EFFECT when that event is
offered (last-edge-wins over the control column), and `collect` keeps exactly
the packets whose in-effect label is `active`.  This decomposition is
structurally distinct from the deployed single fold, so the refinement theorem
`run_sink_spec` is a genuine equational obligation (an induction bridges the two
recursions), not a definitional restatement.

Refinement target: the DEPLOYED function is `Tap.run` (the fold the dataplane
invokes via `Tap.step` on each `.pkt`), observed through its `.sink` log.
`run_sink_spec` binds that function directly.
-/

import Tap.Basic

namespace Tap.NoLeakSpec

open Tap

variable {α : Type}

/-! ### The specification (independent of the implementation)

Two passes over the event trace.  Neither pass mentions any deployed function. -/

/-- The session state that a single control edge leaves behind, applied to the
current state.  `.enable` activates the copy session, `.disable` deactivates it,
and an offered packet leaves the session state untouched (a packet is data, not
a control edge).  This is the last-edge-wins column of the MIB row lifecycle. -/
def nextActive (active : Bool) : Ev α → Bool
  | .enable  => true
  | .disable => false
  | .pkt _   => active

/-- Pass 1 — annotate each event with the session state IN EFFECT when that
event is offered.  The head keeps the entry state `active`; the tail is
annotated under the state the head leaves behind.  `annotate active es` is thus
the sequence of `(state-in-effect, event)` pairs the session steps through. -/
def annotate (active : Bool) : List (Ev α) → List (Bool × Ev α)
  | []      => []
  | e :: es => (active, e) :: annotate (nextActive active e) es

/-- Pass 2 — collect the copied traffic: keep exactly the packets whose
in-effect session state is `active`, in order.  Control edges and packets
offered under an inactive session contribute nothing. -/
def collect : List (Bool × Ev α) → List α
  | []            => []
  | (b, e) :: rest =>
      match b, e with
      | true, .pkt p => p :: collect rest
      | _,    _      => collect rest

/-- The specified diagnostic output over a trace, starting from session state
`active`: the copied packets, per RFC 2613 portCopy semantics. -/
def tapOutput (active : Bool) (es : List (Ev α)) : List α :=
  collect (annotate active es)

/-! ### Spec-side trace predicates and packet reading

Defined independently so the disabled/enabled corollaries below never appeal to
implementation views. -/

/-- The trace contains a session-activation edge. -/
def hasActivate : List (Ev α) → Bool
  | []             => false
  | .enable  :: _  => true
  | _       :: es  => hasActivate es

/-- The trace contains a session-deactivation edge. -/
def hasDeactivate : List (Ev α) → Bool
  | []              => false
  | .disable :: _   => true
  | _        :: es  => hasDeactivate es

/-- Every packet offered on the trace, in order, ignoring session state — the
"exactly the source, no drop, no injection" yardstick for a fully-active
window. -/
def payloads : List (Ev α) → List α
  | []            => []
  | .pkt p :: es  => p :: payloads es
  | _      :: es  => payloads es

/-! ### The refinement theorem — deployed `Tap.run` matches the spec -/

/-- **Refinement (master).**  For every start state and every trace, the sink of
the DEPLOYED fold `Tap.run` is the starting sink followed by exactly the
spec-copied traffic `tapOutput`.  This binds the real `Tap.run`/`Tap.step`
dataplane path to the RFC-2613-derived specification on all inputs.

The proof is a genuine induction reconciling the deployed single fold with the
spec's annotate/collect two-pass; it is not `rfl`. -/
theorem run_sink_spec (s : State α) (es : List (Ev α)) :
    (run s es).sink = s.sink ++ tapOutput s.enabled es := by
  induction es generalizing s with
  | nil => simp [run, tapOutput, annotate, collect]
  | cons e es ih =>
    cases e with
    | pkt p =>
      show (run (step s (.pkt p)) es).sink
          = s.sink ++ tapOutput s.enabled (.pkt p :: es)
      rw [ih (step s (.pkt p)), step_pkt_enabled]
      cases hb : s.enabled with
      | true =>
          simp [step, hb, tapOutput, annotate, collect, nextActive,
                List.append_assoc]
      | false =>
          simp [step, hb, tapOutput, annotate, collect, nextActive]
    | enable =>
      show (run (step s .enable) es).sink
          = s.sink ++ tapOutput s.enabled (.enable :: es)
      rw [ih (step s .enable)]
      simp [step, tapOutput, annotate, collect, nextActive]
    | disable =>
      show (run (step s .disable) es).sink
          = s.sink ++ tapOutput s.enabled (.disable :: es)
      rw [ih (step s .disable)]
      simp [step, tapOutput, annotate, collect, nextActive]

/-! ### Corollaries — the two headline security readings, on deployed `Tap.run` -/

/-- Spec lemma: an inactive session (`active = false`) with no activation edge
copies nothing. -/
theorem tapOutput_inactive :
    ∀ es : List (Ev α), hasActivate es = false → tapOutput false es = [] := by
  intro es
  induction es with
  | nil => intro _; rfl
  | cons e es ih =>
    cases e with
    | pkt p =>
      intro h
      have h' : hasActivate es = false := by simpa [hasActivate] using h
      simpa [tapOutput, annotate, collect, nextActive] using ih h'
    | enable => intro h; simp [hasActivate] at h
    | disable =>
      intro h
      have h' : hasActivate es = false := by simpa [hasActivate] using h
      simpa [tapOutput, annotate, collect, nextActive] using ih h'

/-- Spec lemma: an active session (`active = true`) with no deactivation edge
copies exactly the offered packets, in order. -/
theorem tapOutput_active :
    ∀ es : List (Ev α), hasDeactivate es = false → tapOutput true es = payloads es := by
  intro es
  induction es with
  | nil => intro _; rfl
  | cons e es ih =>
    cases e with
    | pkt p =>
      intro h
      have h' : hasDeactivate es = false := by simpa [hasDeactivate] using h
      simpa [tapOutput, annotate, collect, nextActive, payloads] using ih h'
    | enable =>
      intro h
      have h' : hasDeactivate es = false := by simpa [hasDeactivate] using h
      simpa [tapOutput, annotate, collect, nextActive, payloads] using ih h'
    | disable => intro h; simp [hasDeactivate] at h

/-- **Strong non-leak (deployed).**  From the initial DISABLED state, over any
trace that never activates the session, the deployed sink is EMPTY — not one
packet leaves the dataplane into the diagnostic destination.  A disabled tap
leaks nothing. -/
theorem no_leak_when_disabled (es : List (Ev α)) (h : hasActivate es = false) :
    (run (init : State α) es).sink = [] := by
  rw [run_sink_spec]
  simp [init, tapOutput_inactive es h]

/-- **Faithful capture (deployed).**  From a fresh ENABLED start, over any trace
with no deactivation edge, the deployed sink is EXACTLY the offered packets, in
order — no drop, no injection, no reorder, and nothing outside the active
window. -/
theorem faithful_when_enabled (es : List (Ev α)) (h : hasDeactivate es = false) :
    (run (initOn : State α) es).sink = payloads es := by
  rw [run_sink_spec]
  simp [initOn, tapOutput_active es h]

/-! ### Non-vacuity

The spec is falsifiable against a wrong implementation, and is not the deployed
fold renamed. -/

/-- A LEAKY variant that copies every packet regardless of session state —
exactly the failure mode a diagnostic tap must not have. -/
def leakyCopy : List (Ev Nat) → List Nat
  | []            => []
  | .pkt p :: es  => p :: leakyCopy es
  | _      :: es  => leakyCopy es

/-- Non-vacuity witness: on a trace offered to a DISABLED session, the leaky
variant emits `[1, 2]` while the spec emits `[]`.  Because `run_sink_spec` pins
the deployed sink to the spec, a `Tap.step` that behaved like `leakyCopy` (or
copied anything at all while disabled) would make the theorem UNPROVABLE — the
refinement genuinely rules out the leak. -/
example :
    leakyCopy [.pkt 1, .pkt 2] ≠ tapOutput (init : State Nat).enabled [.pkt 1, .pkt 2] := by
  decide

/-- Non-vacuity witness (capture side): the spec keeps only in-gate packets, so
it distinguishes a captured packet from a dropped one — enable, packet, disable,
packet yields exactly the first packet. -/
example :
    tapOutput (init : State Nat).enabled [.enable, .pkt 1, .disable, .pkt 2] = [1] := by
  decide

/-- Deployed end-to-end sanity: the real fold agrees with the spec on the same
trace (via `run_sink_spec`), and both give `[1]`. -/
example :
    (run (init : State Nat) [.enable, .pkt 1, .disable, .pkt 2]).sink = [1] := by
  decide

end Tap.NoLeakSpec
