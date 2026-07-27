import Proto.Basic
import Proto.Step
import Uring.Basic

/-!
# A0 — the copy-once reactor contract (the interface seed)

The seam that connects two libraries: the sans-IO
connection FSM (`Proto`) and the submission/completion ring (`Uring`). This is
the copy-once interface the Milestone-A protocol lanes build against.

**Copy-once discipline (deliberate, not zero-copy).** A `recvInto bid data`
event means the kernel filled provided-buffer `bid`, and its bytes have been
*materialized* into `data`. The reactor feeds `data` to the FSM (which owns it,
matching `Proto.Input.bytesReceived : Bytes → _`) and then recycles `bid`
*immediately* — the lease is done the moment the bytes are copied. This needs no
read-stability metatheory; zero-copy (holding the lease across the parse, the
X-7 region-readout rung) is a named perf-tier successor, not part of this contract.

What is proven here (the seed's own obligations): the event/output translations
are total, and **recycle-exactly-once-after-copy** holds at the reactor level —
a recv event yields exactly one `recycleBuffer bid` submission, and no other
event yields any. The *full* recycle-exactly-once (composed with the `Uring` LTS
so the recycled `bid` is provably one the client `held`) is Milestone A-compose.
-/

namespace Reactor

open Proto (Bytes)

/-- Reactor ingress events — the completion-queue events at the copy-once
altitude (a recv completion's buffer contents are already materialized). -/
inductive RingEvent where
  /-- The kernel filled provided-buffer `bid`; its bytes are `data`. -/
  | recvInto (bid : Uring.Bid) (data : Bytes)
  | writeReady
  | writeBlocked
  | sendComplete
  | timerFired (slot : Proto.TimerSlot)
  | peerClosed
  | closeRequested
  /-- **The effect-completion edge (the effect-scheduler seam).** A serve effect the
  reactor submitted (`connectUpstream`/`sendUpstream` for a proxy dial, or a cache
  read/write) completed on the ring; `result` is the effect's result bytes (the
  stored response on a cache HIT, `[]` on a MISS, the upstream reply for a dial).
  Unlike the wire events above it does NOT drive the `Proto` connection FSM: its
  bytes are threaded into the SERVE continuation (`Reactor.ServeStep.resumeStep`, via
  `Reactor.DriveCache.driveServe`), which is where the effect result belongs — the
  serve effect program is a layer above the wire FSM. At the wire reactor it is
  inert. -/
  | effectComplete (result : Bytes)
deriving Repr

/-- Reactor submissions — what the reactor asks the ring to do. -/
inductive RingSubmission where
  | submitSend (data : Bytes)
  | submitSendUpstream (fd : Nat) (data : Bytes)
  | connectUpstream (addr : Proto.Addr)
  | recycleBuffer (bid : Uring.Bid)
  | armTimer (slot : Proto.TimerSlot)
  | cancelTimer (slot : Proto.TimerSlot)
  | cancelRecv
  | resumeRecv
  | startTlsOffload
  | closeSock
  | dispatch (req : Proto.Request)
  | deliverBody (sid : Nat) (data : Bytes)
  | deliverFrame (frame : Proto.WsFrame)
deriving Repr

/-- Translate a ring event to the FSM input. Copy-once: the recv completion's
bytes are already owned, so it becomes `bytesReceived`. -/
def toInput : RingEvent → Proto.Input
  | .recvInto _ data => .bytesReceived data
  | .writeReady => .writeReady
  | .writeBlocked => .writeBlocked
  | .sendComplete => .sendComplete
  | .timerFired slot => .timerFired slot
  | .peerClosed => .peerClosed
  | .closeRequested => .closeRequested
  -- Effect completions are NOT wire-FSM inputs (their result bytes are threaded to the
  -- serve continuation, not `Proto.step`); this case exists only so `toInput` is total.
  -- `step` never routes an `effectComplete` through `toInput` — its arm holds the wire
  -- state (see `step`), so this value is unreachable from `step`.
  | .effectComplete _ => .writeReady

/-- Translate one FSM output to a ring submission (faithful, no output dropped).
Note: no FSM output is a buffer recycle — recycling is the reactor's own
copy-once obligation, added in `step`. -/
def ofOutput : Proto.Output → RingSubmission
  | .send data => .submitSend data
  | .sendUpstream fd data => .submitSendUpstream fd data
  | .connectUpstream addr => .connectUpstream addr
  | .startTlsOffload => .startTlsOffload
  | .armTimer slot => .armTimer slot
  | .cancelTimer slot => .cancelTimer slot
  | .cancelRecv => .cancelRecv
  | .resumeRecv => .resumeRecv
  | .close => .closeSock
  | .dispatch req => .dispatch req
  | .deliverBody sid data => .deliverBody sid data
  | .deliverFrame frame => .deliverFrame frame

/-- Is this submission a buffer recycle? -/
def RingSubmission.isRecycle : RingSubmission → Bool
  | .recycleBuffer _ => true
  | _ => false

/-- **The copy-once reactor step.** Run the FSM on the event, translate every
output to a submission, and — on a recv completion — append the recycle of that
buffer (the bytes were copied into the FSM accumulation, so the lease is done). -/
def step (cfg : Proto.Config) (s : Proto.State) (e : RingEvent) :
    Proto.State × List RingSubmission :=
  match e with
  | .effectComplete _ =>
      -- An effect completion is NOT a wire-FSM input: its result bytes are threaded
      -- into the SERVE continuation (`Reactor.DriveCache.driveServe` → `resumeStep`),
      -- not `Proto.step`. At the wire reactor it is inert — no submission, no state
      -- change — so the copy-once discipline below is untouched.
      (s, [])
  | .recvInto bid data =>
      let r := Proto.step cfg s (.bytesReceived data)
      (r.1, r.2.map ofOutput ++ [RingSubmission.recycleBuffer bid])
  | e =>
      let r := Proto.step cfg s (toInput e)
      (r.1, r.2.map ofOutput)

/-- No FSM output translates to a buffer recycle — recycling is exclusively the
reactor's copy-once obligation. -/
theorem ofOutput_not_recycle (o : Proto.Output) :
    (ofOutput o).isRecycle = false := by
  cases o <;> rfl

/-- The translated FSM outputs contain no recycle submissions. -/
theorem map_ofOutput_no_recycle (outs : List Proto.Output) :
    (outs.map ofOutput).filter RingSubmission.isRecycle = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨o, _, rfl⟩ := hx
  simp [ofOutput_not_recycle o]

/-- **Recycle-exactly-once-after-copy (reactor level).** A recv completion yields
exactly one buffer-recycle submission, and it is the recycle of *that* buffer.
(The full property — that `bid` was one the client `held` in the ring — is
Milestone A-compose, composing this with the `Uring` LTS.) -/
theorem recv_recycles_exactly_once (cfg : Proto.Config) (s : Proto.State)
    (bid : Uring.Bid) (data : Bytes) :
    ((step cfg s (.recvInto bid data)).2.filter RingSubmission.isRecycle)
      = [RingSubmission.recycleBuffer bid] := by
  simp only [step, List.filter_append, map_ofOutput_no_recycle, List.nil_append]
  rfl

/-- **No spurious recycles.** A non-recv event yields no buffer recycle at all —
the reactor only ever recycles a buffer it was just handed. -/
theorem non_recv_no_recycle (cfg : Proto.Config) (s : Proto.State) (e : RingEvent)
    (h : ∀ bid data, e ≠ .recvInto bid data) :
    (step cfg s e).2.filter RingSubmission.isRecycle = [] := by
  cases e with
  | recvInto bid data => exact absurd rfl (h bid data)
  | effectComplete r => rfl
  | _ => simp only [step]; exact map_ofOutput_no_recycle _

/-! **Totality is not a theorem in Lean.** `step : Config → State → RingEvent → _` is a plain `def`, so
totality is a TYPE-LEVEL fact — the elaborator admits no partial `def` of that
signature, and there is nothing left to prove. The theorem that stood here,
`step_total : step cfg s e = step cfg s e`, was exactly that non-statement:
it holds of EVERY function of the same arity, so it constrained `step` not at
all while wearing a name that claimed it did. The real facts about the step are `non_recv_no_recycle` above. -/

end Reactor
