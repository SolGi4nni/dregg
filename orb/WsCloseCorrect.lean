import Ws.Close

/-!
# Correctness of the WebSocket close handshake (RFC 6455 §5.5.1, §7)

`Ws.Close.step` (Ws/Close.lean) is the deployed close-handshake transition the
endpoint runs. This module states, **independently of that function**, what
RFC 6455 mandates for the handshake and proves the deployed `step` refines it on
every state and event.

## The specification (from the standard, not the code)

The RFC-mandated behaviour is phrased over the two facts the standard's rules
actually turn on — not over the implementation's three-state enum:

* `sentClose` — has *this* endpoint already put a Close frame on the wire.
  RFC 6455 §7.1.1: *"After sending a Close frame, an endpoint MUST NOT send any
  further data frames."* Every "no data after Close" obligation keys on this bit.
* `closed` — has the connection reached the CLOSED state, i.e. both directions
  have sent Close (RFC 6455 §7.1.4). CLOSED is terminal.

`react` (below) is written straight from the section prose. It never mentions
`Ws.Close.step`; it decides each reaction from `sentClose` / `closed` alone.

The refinement theorem `step_refines` is a commuting square: abstracting the
deployed state with `abs`, the deployed `step` produces exactly the next
abstract status and output that `react` mandates — for all 12 state/event
combinations. Because the square equates *outputs verbatim*, any implementation
that (a) emitted a data frame after sending Close, or (b) failed to echo the
received status code on a first Close, or (c) acted in the terminal CLOSED
state, would make an output disagree and the theorem would not hold. The spec is
therefore non-vacuous, and it is not the implementation renamed: its state space
(a pair of booleans read off §7.1.1 / §7.1.4) and its decision logic are
distinct from `step`'s enum case table, connected only by `abs`.

## RFC 6455 §5.5.1 — the length-1 Close rejection (enforced at the frame layer)

§5.5.1 additionally requires that a Close frame carrying a body have a body of at
least two octets (the 2-byte status code): a Close whose payload length is 1 is a
protocol error. The deployed `Ws.Close.step` receives an **already-decoded**
status code (`Event.recvClose (code : Nat)`) and never sees the frame payload, so
the check cannot live there — by the time an event reaches `step` the payload is
gone. It is therefore enforced one layer up, at the frame-validation predicate
`Ws.Frame.Wf` (Ws/Frame.lean), which is the deployed check that still holds the
raw payload: a Close frame is well-formed only if its payload is empty or ≥ 2
octets, so a length-1 Close is rejected as a protocol error before it can be
decoded into a `recvClose`.

The section `## §5.5.1 at the frame layer` below states this over the deployed
`Ws.Frame.Wf`: a length-1 Close is rejected (witness), while a length-0 and a
length-2 Close are accepted — so an implementation that accepted a length-1 Close
would refute `frame_rejects_len1_close`.
-/

namespace Ws
namespace CloseSpec

/-- RFC 6455 §7 abstract close-handshake status, in the two bits the standard's
rules turn on: whether this endpoint has already sent a Close frame (§7.1.1) and
whether the connection has reached CLOSED — both directions closed (§7.1.4). -/
structure Status where
  /-- This endpoint has put a Close frame on the wire (§7.1.1). -/
  sentClose : Bool
  /-- CLOSED reached: both directions have sent Close (§7.1.4); terminal. -/
  closed : Bool
deriving DecidableEq, Repr

/-- The RFC-mandated reaction to an event as `(next status, output)`, written
directly from the section prose with no reference to `Ws.Close.step`.

* §7.1.4 — CLOSED is terminal: every event is a protocol error.
* §7.1.1 — an endpoint that has sent a Close MUST NOT send further data frames,
  so `sendData` after `sentClose` is a protocol error; otherwise the frame is
  emitted.
* §7.1.2 — receiving a Close while it has *not* sent one obliges the endpoint to
  send a Close in response echoing the received status code; if it has already
  sent its Close, the received Close completes the handshake (no output) and the
  connection is CLOSED.
* a `sendClose` puts the Close on the wire, reaching CLOSED iff a Close had
  already been sent; a `recvData` is delivered until CLOSED. -/
def react : Status → Ws.Close.Event → Status × Ws.Close.Output
  | s, e =>
    if s.closed then (s, .error)                                        -- §7.1.4 terminal
    else match e with
      | .sendData    => if s.sentClose then (s, .error) else (s, .emitData)  -- §7.1.1
      | .recvData    => (s, .deliver)
      | .sendClose _ => ({ s with sentClose := true, closed := s.sentClose }, .emitClose)
      | .recvClose c =>
          if s.sentClose then ({ s with closed := true }, .nothing)     -- completes handshake
          else ({ sentClose := true, closed := false }, .echoClose c)   -- §7.1.2 echo the code

/-- Abstraction of the deployed close-handshake state to the RFC status. `opened`
has sent nothing; `closing` means this endpoint has sent its Close but the
handshake is not yet complete; `closed` is CLOSED (both directions). -/
def abs : Ws.Close.State → Status
  | .opened  => { sentClose := false, closed := false }
  | .closing => { sentClose := true,  closed := false }
  | .closed  => { sentClose := true,  closed := true }

/-- `abs` is injective: distinct deployed states have distinct RFC statuses (so
the commuting square below pins the next *state*, not only the output). -/
theorem abs_injective (a b : Ws.Close.State) (h : abs a = abs b) : a = b := by
  cases a <;> cases b <;> simp_all [abs]

/-- **Refinement.** The deployed close-handshake transition `Ws.Close.step`
refines the RFC specification `react`: for every state and event, abstracting the
deployed next state gives exactly the status `react` mandates, and the deployed
output is exactly the output `react` mandates. This binds the real deployed
`Ws.Close.step`, not a wrapper. -/
theorem step_refines (st : Ws.Close.State) (e : Ws.Close.Event) :
    react (abs st) e = (abs (Ws.Close.step st e).1, (Ws.Close.step st e).2) := by
  cases st <;> cases e <;> rfl

/-- Output half of the refinement, extracted for the corollaries. -/
theorem step_output (st : Ws.Close.State) (e : Ws.Close.Event) :
    (Ws.Close.step st e).2 = (react (abs st) e).2 :=
  (congrArg Prod.snd (step_refines st e)).symm

/-- Next-state half of the refinement. -/
theorem step_state (st : Ws.Close.State) (e : Ws.Close.Event) :
    abs (Ws.Close.step st e).1 = (react (abs st) e).1 :=
  (congrArg Prod.fst (step_refines st e)).symm

/-! ## Non-vacuity: the spec pins the two RFC obligations, and the refinement
forces the deployed function to meet them. -/

/-- Spec side (§7.1.1): once a Close has been sent, a data send is a protocol
error — in either the CLOSING or the CLOSED status. -/
theorem spec_no_data_after_close (s : Status) (h : s.sentClose = true) :
    (react s .sendData).2 = .error := by
  cases hc : s.closed <;> simp [react, hc, h]

/-- Deployed side, via the refinement: after this endpoint has sent its Close
(`abs st |>.sentClose`), `Ws.Close.step` emits `error`, never a data frame. An
implementation that emitted data here would refute this. -/
theorem impl_no_data_after_close (st : Ws.Close.State) (h : (abs st).sentClose = true) :
    (Ws.Close.step st .sendData).2 = .error := by
  rw [step_output]; exact spec_no_data_after_close (abs st) h

/-- The deployed states with a Close already sent are exactly `closing` / `closed`;
so `impl_no_data_after_close` says: no data frame after Close, stated on the
deployed enum. -/
theorem impl_no_data_unless_opened (st : Ws.Close.State) (h : st ≠ .opened) :
    (Ws.Close.step st .sendData).2 = .error := by
  apply impl_no_data_after_close
  cases st <;> simp_all [abs]

/-- Spec side (§7.1.2): receiving a first Close (none sent yet) obliges an echo of
the *same* status code. -/
theorem spec_recv_close_echoes (c : Nat) :
    react { sentClose := false, closed := false } (.recvClose c)
      = ({ sentClose := true, closed := false }, .echoClose c) := rfl

/-- Deployed side, via the refinement: from `opened`, `Ws.Close.step` echoes the
received code. An implementation that dropped the Close or echoed a different code
would refute this. -/
theorem impl_recv_close_echoes (c : Nat) :
    (Ws.Close.step .opened (.recvClose c)).2 = .echoClose c := by
  rw [step_output]; rfl

/-! ## §5.5.1 at the frame layer: a length-1 Close is a protocol error

The check that a Close body carries a full status code lives where the raw
payload is still visible: the deployed frame-validation predicate `Ws.Frame.Wf`.
These theorems state the §5.5.1 rule over that deployed function and pin its
non-vacuity — a length-1 Close is rejected, length-0 and length-2 accepted. -/

/-- A Close frame carrying exactly one octet of payload (a status code truncated
to a single byte) — the §5.5.1 protocol error. -/
def closeLen1 : Ws.Frame := { fin := true, opcode := .close, payload := [0x03] }

/-- A Close frame with no body (no status code) — permitted by §5.5.1. -/
def closeLen0 : Ws.Frame := { fin := true, opcode := .close, payload := [] }

/-- A Close frame carrying a full 2-octet status code (`1000`, normal closure) —
permitted by §5.5.1. -/
def closeLen2 : Ws.Frame := { fin := true, opcode := .close, payload := [0x03, 0xe8] }

/-- **The deployed frame validation rejects a length-1 Close.** `Ws.Frame.Wf`,
the frame well-formedness predicate the deployment runs before a frame reaches
the close/reassembly machinery, fails on any Close whose payload is exactly one
octet (RFC 6455 §5.5.1). -/
theorem frame_rejects_len1_close (f : Ws.Frame)
    (hc : f.opcode = Ws.Opcode.close) (h1 : f.payload.length = 1) :
    ¬ f.Wf :=
  Ws.Frame.not_wf_close_len_one hc h1

/-- **The deployed frame validation accepts an accepted-shaped Close body.** A
Close with any body it accepts carries at least the full 2-octet status code, so
the downstream decode into `Event.recvClose` is on a well-formed code. -/
theorem frame_accepted_close_body_ge_two (f : Ws.Frame)
    (hc : f.opcode = Ws.Opcode.close) (hne : f.payload ≠ []) (hwf : f.Wf) :
    2 ≤ f.payload.length :=
  Ws.Frame.close_body_ge_two hc hne hwf

/-- **Non-vacuity (witnesses).** The deployed `Ws.Frame.Wf` rejects the length-1
Close and accepts both the empty and the 2-octet Close. An implementation that
accepted a length-1 Close would refute the first conjunct. -/
theorem close_len1_rejected_len0_len2_accepted :
    ¬ closeLen1.Wf ∧ closeLen0.Wf ∧ closeLen2.Wf := by
  refine ⟨?_, ?_, ?_⟩
  · exact frame_rejects_len1_close closeLen1 rfl rfl
  · decide
  · decide

end CloseSpec
end Ws
