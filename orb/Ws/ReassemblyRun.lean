import Ws.Reassembly

/-!
# WebSocket reassembly — multi-step trajectory invariants (RFC 6455 §5.4/§5.5)

`Ws.Reassembly` proves the fragmentation step FSM one frame at a time: a control
frame leaves the reassembly state untouched (`step_control_state`), a fresh data
frame mid-fragment is a protocol error, and a delivered message is the in-order
concatenation of its fragments. Those are **single-step** facts.

This module lifts the safety-critical ones to whole **trajectories** — arbitrary
sequences of frames folded through `step` — because the interleaving is exactly
what a peer controls. `runState` folds a frame list through `Reassembly.step`,
threading the reassembly state (the output of each step is the observable; the
state is what the next frame sees).

The theorems:

* `step_message_fin` / `step_absorbed_not_fin` — **no invalid delivery**: from
  any state, the step emits a completed `message` only on a FIN frame and marks
  a frame `absorbed` only when it is non-FIN. A message boundary is never
  manufactured mid-frame.
* `runState_preserves_stateWf` / `runState_assembling_isData` — **the
  message-opcode invariant, preserved across every transition**: any assembling
  state reachable from `idle` by an arbitrary frame sequence carries a *data*
  opcode (`text`/`binary`), never a continuation, control, or reserved opcode.
  The reassembler never mislabels the message it is building.
* `runState_filter_control` — **a control frame never splits a fragmented
  message**: deleting every control frame from a trajectory leaves the final
  reassembly state identical. A ping/pong/close interleaved anywhere among a
  message's fragments is transparent to the reassembly in progress (§5.5) for
  the whole run, not just for one step.
-/

namespace Ws
namespace Reassembly

/-- Fold a frame list through `step`, threading the reassembly state. -/
def runState (st : State) : List Frame → State
  | [] => st
  | f :: fs => runState (step st f).1 fs

@[simp] theorem runState_nil (st : State) : runState st [] = st := rfl

@[simp] theorem runState_cons (st : State) (f : Frame) (fs : List Frame) :
    runState st (f :: fs) = runState (step st f).1 fs := rfl

/-! ## No invalid delivery -/

/-- **A message is delivered only on a FIN frame.** From any state, if the step
emits a completed `message`, the driving frame carried the FIN bit — the FSM
never manufactures a message boundary mid-frame. -/
theorem step_message_fin (st : State) (f : Frame) {op : Opcode} {pl : Bytes}
    (h : (step st f).2 = .message op pl) : f.fin = true := by
  obtain ⟨fin, opc, payl⟩ := f
  cases fin
  · cases opc <;> cases st <;> simp_all [step, Opcode.isControl]
  · rfl

/-- **A frame is absorbed only when it is non-FIN.** Dual to `step_message_fin`:
a buffered-but-not-delivered frame never carried FIN. -/
theorem step_absorbed_not_fin (st : State) (f : Frame)
    (h : (step st f).2 = .absorbed) : f.fin = false := by
  obtain ⟨fin, opc, payl⟩ := f
  cases fin
  · rfl
  · cases opc <;> cases st <;> simp_all [step, Opcode.isControl]

/-! ## The message-opcode invariant, preserved across every transition -/

/-- The state well-formedness invariant: an in-progress message carries a *data*
opcode (`text` or `binary`); `idle` is trivially well-formed. -/
def StateWf : State → Prop
  | .idle => True
  | .assembling p => p.opcode = .text ∨ p.opcode = .binary

/-- `idle` is well-formed. -/
theorem stateWf_idle : StateWf .idle := trivial

/-- **The invariant is preserved by every transition.** If the pre-state is
well-formed then so is the post-state — for any frame, any opcode, any FIN. -/
theorem step_preserves_stateWf (st : State) (f : Frame) (h : StateWf st) :
    StateWf (step st f).1 := by
  obtain ⟨fin, opc, payl⟩ := f
  cases opc <;> cases st <;> (try cases fin) <;>
    simp_all [step, StateWf, Opcode.isControl]

/-- **The invariant over a whole trajectory.** From a well-formed state, every
state reachable by folding any frame sequence is well-formed. -/
theorem runState_preserves_stateWf (st : State) (fs : List Frame)
    (h : StateWf st) : StateWf (runState st fs) := by
  induction fs generalizing st with
  | nil => simpa using h
  | cons f fs ih => exact ih (step st f).1 (step_preserves_stateWf st f h)

/-- **Headline: the reassembler never mislabels the message it is building.**
Any assembling state reachable from `idle` by an arbitrary frame sequence carries
a data opcode — `text` or `binary`, never a continuation/control/reserved
opcode. -/
theorem runState_assembling_isData (fs : List Frame) (p : Partial)
    (h : runState .idle fs = .assembling p) :
    p.opcode = .text ∨ p.opcode = .binary := by
  have hw := runState_preserves_stateWf .idle fs stateWf_idle
  rw [h] at hw
  simpa [StateWf] using hw

/-! ## A control frame never splits a fragmented message -/

/-- **Control frames are transparent to the whole trajectory.** Deleting every
control frame from a frame sequence leaves the final reassembly state unchanged:
a ping/pong/close interleaved anywhere among a message's fragments cannot disturb
the reassembly in progress (§5.5), across the entire run — not just one step. -/
theorem runState_filter_control (st : State) (fs : List Frame) :
    runState st (fs.filter (fun g => ! g.opcode.isControl)) = runState st fs := by
  induction fs generalizing st with
  | nil => rfl
  | cons f fs ih =>
    by_cases hc : f.opcode.isControl = true
    · have hfil : (f :: fs).filter (fun g => ! g.opcode.isControl)
              = fs.filter (fun g => ! g.opcode.isControl) := by
        simp [List.filter_cons, hc]
      rw [hfil, runState_cons, step_control_state st f hc]
      exact ih st
    · have hnc : f.opcode.isControl = false := by simpa using hc
      have hfil : (f :: fs).filter (fun g => ! g.opcode.isControl)
              = f :: fs.filter (fun g => ! g.opcode.isControl) := by
        simp [List.filter_cons, hnc]
      rw [hfil]
      simp only [runState_cons]
      exact ih (step st f).1

/-! ## Witnesses (non-vacuity) -/

/-- A ping between two fragments of a binary message is transparent: the
reassembly reaches the same state as if the ping were absent (an instance of
`runState_filter_control` with concrete frames). -/
example (a b : Bytes) :
    runState .idle
        [⟨false, .binary, a⟩, ⟨true, .ping, []⟩, ⟨true, .continuation, b⟩]
      = runState .idle
        [⟨false, .binary, a⟩, ⟨true, .continuation, b⟩] := by
  simp [runState, step, Opcode.isControl]

/-- The opcode invariant bites on a real assembling state: after an opening
binary fragment the reassembler is assembling a `binary` message, so the
invariant discharges to the `binary` disjunct on a non-empty reachable set. -/
example (a : Bytes) :
    runState .idle [⟨false, .binary, a⟩] = .assembling { opcode := .binary, acc := a } := by
  simp [runState, step, Opcode.isControl]

end Reassembly
end Ws
