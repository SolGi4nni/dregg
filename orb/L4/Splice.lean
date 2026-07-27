/-!
# L4.Splice — the zero-copy layer-4 relay (a model of the kernel `splice`)

`Reactor.L4` moves an L4 stream verbatim, but through the reactor's *copy*
vocabulary: every client chunk becomes a `submitSendUpstream fd d` and every
upstream chunk a `submitSend d` — the bytes `d` ride in the submission, i.e.
they are materialized in the process's address space on the way through. That
is the plain relay: correct, but it pays one userspace copy per chunk per
direction.

This file models the *zero-copy* relay: the bytes never enter userspace at
all. In the kernel, `splice(2)` moves data between a file descriptor and a
pipe without a userspace round-trip; a full fd→fd relay is a pair of splices,
`socket → pipe` (the **pull** phase) and `pipe → socket` (the **push** phase),
run continuously per direction until end-of-stream. A connection carries two
pipes — one per direction — so four kernel byte-streams (client fd, upstream
fd, and the two pipe buffers), and the relay is a schedule of splice
operations over them. The operation the relay issues is `splice src dst len`:
a *source* fd, a *destination* fd, and a length. It carries **no bytes** — the
whole point.

Two properties are proven here.

**`splice_relay_faithful`** — for *both* directions, when the relay has drained
(source fds at EOF and pipes emptied), the bytes delivered to each destination
fd equal that direction's source stream, verbatim and in order. The proof is a
kernel-side conservation law: `atDst ++ inPipe ++ atSrc` is invariant under
every pull and every push, so once `inPipe` and `atSrc` are empty, `atDst` is
the whole original stream. This holds for *any* schedule of pull/push
operations with *any* chunk sizes and *any* interleaving of the two
directions — not a fixed ceremony. A pull that dropped a byte, a push that
reordered the pipe, or a stray extra splice would each break the invariant.

**`splice_no_userspace_copy`** — the relay's emitted operation stream
materializes zero bytes in userspace. The op language *can* express a userspace
copy (`RelayOp.userCopy dst data`, the plain-relay alternative — bytes in the
op), and the byte-footprint projection charges exactly those bytes; the splice
relay emits only `RelayOp.splice`, whose footprint is empty, so the whole
relay's footprint is `[]`. `userCopy_would_materialize` is the contrast: the
same projection over a plain-relay op carrying real bytes is non-empty — the
copy the splice path removes.

`pump_faithful` / `pump_relay_faithful` discharge the drained hypotheses with a
concrete, whole-stream schedule, so the faithfulness theorems are witnessed on
real inputs rather than asserted vacuously.

**Follow-on (named, not modeled here).** The syscall shell wiring: on the
Linux `io_uring` datapath, per accepted L4 connection issue `pipe2(O_NONBLOCK)`
twice (one pipe per direction) and submit the initial `IORING_OP_SPLICE`
socket→pipe pull for each direction, with a completion tag encoding
`(client_fd, direction, phase)`; on each completion, chain the opposite phase
(pull→push→pull…), treating `bytes_moved == 0` as EOF and applying the
per-direction half-close (`shutdown(SHUT_WR)` on the paired socket, full close
once both directions have seen EOF). That is the `submit_splice` /
`on_splice_complete` shell driving exactly the schedule this file proves
faithful; it is C/Rust FFI against the ring, out of the Lean TCB.
-/

namespace L4.Splice

/-- A byte stream. Element type is immaterial to every theorem here (all the
reasoning is `List` conservation); bytes are `UInt8` to match the wire. -/
abbrev Bytes := List UInt8

/-! ## The kernel byte-move operation the relay emits

The relay issues `splice src dst len` — fd numbers and a length, **no
payload**. `userCopy` is the *plain* relay's alternative (the copy the
zero-copy path exists to remove): it carries the bytes. Keeping both in one
type makes "materializes nothing" a real claim about a language that *could*
materialize, not a triviality. -/
inductive RelayOp where
  /-- Kernel fd→fd move (a `splice(2)`): source fd, destination fd, length.
      No bytes cross userspace. -/
  | splice (src : Nat) (dst : Nat) (len : Nat)
  /-- The plain relay's copying send: the bytes live in the op (userspace). -/
  | userCopy (dst : Nat) (data : Bytes)
deriving Repr, DecidableEq

/-- The bytes an operation stream materializes in userspace, in order. A
`splice` contributes nothing (the bytes stay in kernel space); a `userCopy`
contributes its whole payload. -/
def userspaceBytes : List RelayOp → Bytes
  | [] => []
  | .splice _ _ _ :: rest => userspaceBytes rest
  | .userCopy _ d :: rest => d ++ userspaceBytes rest

theorem userspaceBytes_append (xs ys : List RelayOp) :
    userspaceBytes (xs ++ ys) = userspaceBytes xs ++ userspaceBytes ys := by
  induction xs with
  | nil => rfl
  | cons x rest ih => cases x <;> simp [userspaceBytes, ih, List.append_assoc]

/-! ## One direction: a kernel channel through a pipe

A directional relay owns three kernel byte-streams: what is still readable at
the source fd (`atSrc`), what currently sits in the pipe buffer (`inPipe`), and
what has been delivered to the destination fd (`atDst`). None of these is in
userspace. -/
structure Chan where
  /-- Bytes still readable at the source fd (kernel side). -/
  atSrc  : Bytes
  /-- Bytes currently buffered in the kernel pipe. -/
  inPipe : Bytes
  /-- Bytes delivered to the destination fd, in order. -/
  atDst  : Bytes
deriving Repr, DecidableEq

/-- **Pull** (`socket → pipe`): move the first `len` readable bytes from the
source fd into the tail of the pipe. -/
def pull (len : Nat) (c : Chan) : Chan :=
  { atSrc := c.atSrc.drop len, inPipe := c.inPipe ++ c.atSrc.take len, atDst := c.atDst }

/-- **Push** (`pipe → socket`): move the first `len` bytes out of the pipe into
the tail of the destination fd. -/
def push (len : Nat) (c : Chan) : Chan :=
  { atSrc := c.atSrc, inPipe := c.inPipe.drop len, atDst := c.atDst ++ c.inPipe.take len }

/-- A splice phase over one channel. -/
inductive Phase where
  /-- `socket → pipe`, moving `len` bytes. -/
  | pull (len : Nat)
  /-- `pipe → socket`, moving `len` bytes. -/
  | push (len : Nat)
deriving Repr, DecidableEq

/-- Run one phase against a channel. -/
def stepChan : Chan → Phase → Chan
  | c, .pull n => pull n c
  | c, .push n => push n c

/-- Run a schedule of phases against a channel. -/
def runChan (c : Chan) : List Phase → Chan
  | []      => c
  | p :: ps => runChan (stepChan c p) ps

/-- **Conservation, one step.** No pull or push creates, loses, duplicates, or
reorders a byte: the concatenation `atDst ++ inPipe ++ atSrc` — everything that
is downstream, in flight, or still upstream — is invariant. -/
theorem stepChan_conserves (c : Chan) (p : Phase) :
    (stepChan c p).atDst ++ (stepChan c p).inPipe ++ (stepChan c p).atSrc
      = c.atDst ++ c.inPipe ++ c.atSrc := by
  cases p with
  | pull n =>
    simp only [stepChan, pull, List.append_assoc, List.take_append_drop]
  | push n =>
    simp only [stepChan, push, List.append_assoc, List.take_append_drop]

/-- **Conservation, whole schedule.** The invariant survives any run. -/
theorem runChan_conserves (c : Chan) (ps : List Phase) :
    (runChan c ps).atDst ++ (runChan c ps).inPipe ++ (runChan c ps).atSrc
      = c.atDst ++ c.inPipe ++ c.atSrc := by
  induction ps generalizing c with
  | nil => rfl
  | cons p ps ih => rw [runChan, ih (stepChan c p), stepChan_conserves]

/-- A fresh channel for a source `stream`: nothing spliced yet. -/
def freshChan (stream : Bytes) : Chan := ⟨stream, [], []⟩

/-- **One-direction faithfulness.** Start a channel on `stream`; run any splice
schedule; if the source is at EOF (`atSrc = []`) and the pipe is drained
(`inPipe = []`), the destination fd has received exactly `stream`, verbatim and
in order. -/
theorem splice_faithful (stream : Bytes) (ps : List Phase)
    (hPipe : (runChan (freshChan stream) ps).inPipe = [])
    (hSrc  : (runChan (freshChan stream) ps).atSrc = []) :
    (runChan (freshChan stream) ps).atDst = stream := by
  have hc := runChan_conserves (freshChan stream) ps
  rw [hPipe, hSrc] at hc
  simpa [freshChan] using hc

/-! ## Both directions: the connection relay

A whole L4 connection runs two directional channels — client→upstream (`c2u`)
and upstream→client (`u2c`) — over two independent pipes. The relay interleaves
their phases arbitrarily (the ring completes them as data arrives). -/
structure Relay where
  /-- Client → upstream channel. -/
  c2u : Chan
  /-- Upstream → client channel. -/
  u2c : Chan
deriving Repr, DecidableEq

/-- A phase tagged with the direction it acts on. -/
inductive BiPhase where
  /-- Act on the client→upstream channel. -/
  | up   (p : Phase)
  /-- Act on the upstream→client channel. -/
  | down (p : Phase)
deriving Repr, DecidableEq

/-- Run one tagged phase; the untouched direction is left exactly as it was. -/
def stepRelay : Relay → BiPhase → Relay
  | r, .up p   => { r with c2u := stepChan r.c2u p }
  | r, .down p => { r with u2c := stepChan r.u2c p }

/-- Run an interleaved schedule of both directions. -/
def runRelay (r : Relay) : List BiPhase → Relay
  | []      => r
  | b :: bs => runRelay (stepRelay r b) bs

/-- The client→upstream phases of an interleaved schedule. -/
def projUp : List BiPhase → List Phase
  | []            => []
  | .up p :: bs   => p :: projUp bs
  | .down _ :: bs => projUp bs

/-- The upstream→client phases of an interleaved schedule. -/
def projDown : List BiPhase → List Phase
  | []            => []
  | .down p :: bs => p :: projDown bs
  | .up _ :: bs   => projDown bs

/-- The two directions are independent: the c2u channel after an interleaved
run is exactly the c2u channel run on its own projected phases. -/
theorem runRelay_c2u (r : Relay) (bs : List BiPhase) :
    (runRelay r bs).c2u = runChan r.c2u (projUp bs) := by
  induction bs generalizing r with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | up p   => simp [runRelay, stepRelay, projUp, runChan, ih]
    | down p => simp [runRelay, stepRelay, projDown, projUp, runChan, ih]

/-- Mirror of `runRelay_c2u` for the upstream→client channel. -/
theorem runRelay_u2c (r : Relay) (bs : List BiPhase) :
    (runRelay r bs).u2c = runChan r.u2c (projDown bs) := by
  induction bs generalizing r with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | up p   => simp [runRelay, stepRelay, projUp, projDown, runChan, ih]
    | down p => simp [runRelay, stepRelay, projDown, runChan, ih]

/-- A fresh relay for the two source streams. -/
def freshRelay (clientStream upstreamStream : Bytes) : Relay :=
  ⟨freshChan clientStream, freshChan upstreamStream⟩

/-- **The zero-copy L4 relay is byte-faithful in both directions.** Over any
interleaved schedule of splice phases, once both directions have drained
(sources at EOF, pipes empty), the client→upstream destination has received the
client's stream verbatim and the upstream→client destination has received the
upstream's stream verbatim — every byte, in order, nothing invented, nothing
dropped, nothing reordered. -/
theorem splice_relay_faithful
    (clientStream upstreamStream : Bytes) (bs : List BiPhase)
    (hUpPipe : (runRelay (freshRelay clientStream upstreamStream) bs).c2u.inPipe = [])
    (hUpSrc  : (runRelay (freshRelay clientStream upstreamStream) bs).c2u.atSrc = [])
    (hDownPipe : (runRelay (freshRelay clientStream upstreamStream) bs).u2c.inPipe = [])
    (hDownSrc  : (runRelay (freshRelay clientStream upstreamStream) bs).u2c.atSrc = []) :
    (runRelay (freshRelay clientStream upstreamStream) bs).c2u.atDst = clientStream
    ∧ (runRelay (freshRelay clientStream upstreamStream) bs).u2c.atDst = upstreamStream := by
  rw [runRelay_c2u] at hUpPipe hUpSrc
  rw [runRelay_u2c] at hDownPipe hDownSrc
  rw [runRelay_c2u, runRelay_u2c]
  exact ⟨splice_faithful clientStream (projUp bs) hUpPipe hUpSrc,
         splice_faithful upstreamStream (projDown bs) hDownPipe hDownSrc⟩

/-! ## Zero-copy: the emitted operation stream materializes no bytes

The relay's fd map: the client and upstream sockets, and the read/write ends of
the two pipes. -/
structure Fds where
  /-- Accepted client socket. -/
  clientFd   : Nat
  /-- Dialed upstream socket. -/
  upstreamFd : Nat
  /-- Read end of the client→upstream pipe. -/
  c2uRead    : Nat
  /-- Write end of the client→upstream pipe. -/
  c2uWrite   : Nat
  /-- Read end of the upstream→client pipe. -/
  u2cRead    : Nat
  /-- Write end of the upstream→client pipe. -/
  u2cWrite   : Nat

/-- The kernel operation a single relay phase emits. Every case is a `splice`
between two fds — a socket and a pipe end — carrying only a length. The pull
phase splices `socket → pipe`; the push phase splices `pipe → socket`. No
branch ever emits a `userCopy`: no bytes are placed in userspace. -/
def emit (f : Fds) : BiPhase → RelayOp
  | .up   (.pull n) => .splice f.clientFd   f.c2uWrite n   -- client socket → c2u pipe
  | .up   (.push n) => .splice f.c2uRead    f.upstreamFd n -- c2u pipe → upstream socket
  | .down (.pull n) => .splice f.upstreamFd f.u2cWrite n   -- upstream socket → u2c pipe
  | .down (.push n) => .splice f.u2cRead    f.clientFd  n  -- u2c pipe → client socket

/-- The whole operation stream the relay submits for a schedule. -/
def emitAll (f : Fds) : List BiPhase → List RelayOp
  | []      => []
  | b :: bs => emit f b :: emitAll f bs

/-- **Zero userspace copy.** Whatever the schedule, the relay's emitted
operation stream materializes no bytes in the process address space: its
userspace byte-footprint is empty. The bytes move fd→pipe→fd inside the kernel;
userspace only ever names fds and lengths. -/
theorem splice_no_userspace_copy (f : Fds) (bs : List BiPhase) :
    userspaceBytes (emitAll f bs) = [] := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hsplice : ∀ b', ∃ s d n, emit f b' = .splice s d n := by
      intro b'; cases b' with
      | up p   => cases p <;> exact ⟨_, _, _, rfl⟩
      | down p => cases p <;> exact ⟨_, _, _, rfl⟩
    obtain ⟨s, d, n, he⟩ := hsplice b
    simp [emitAll, he, userspaceBytes, ih]

/-- **The copy the splice path removes.** The very same op language expresses a
plain-relay copying send, and its userspace footprint is exactly the bytes it
carries — non-empty whenever there is real data. This is the per-chunk copy the
zero-copy relay avoids; the contrast is what makes `splice_no_userspace_copy` a
claim rather than a tautology. -/
theorem userCopy_would_materialize (dst : Nat) (d : Bytes) (rest : List RelayOp)
    (hd : d ≠ []) : userspaceBytes (.userCopy dst d :: rest) ≠ [] := by
  simp only [userspaceBytes]
  intro hcontra
  exact hd (List.append_eq_nil_iff.mp hcontra).1

/-! ## Non-vacuity: a concrete drain schedule witnesses the hypotheses

`splice_faithful` and `splice_relay_faithful` are stated over *any* schedule
that happens to drain. A whole-stream pump — pull the entire source into the
pipe, then push the entire pipe to the destination — drains for every stream,
so the drained hypotheses are inhabited on real, symbolic input, not just
assumed. -/

/-- Pull the whole source, then push the whole pipe. -/
def pumpSchedule (stream : Bytes) : List Phase :=
  [.pull stream.length, .push stream.length]

/-- The whole-stream pump drains: source at EOF, pipe empty. -/
theorem pump_drains (stream : Bytes) :
    (runChan (freshChan stream) (pumpSchedule stream)).inPipe = []
    ∧ (runChan (freshChan stream) (pumpSchedule stream)).atSrc = [] := by
  simp [pumpSchedule, runChan, stepChan, pull, push, freshChan,
        List.take_length, List.drop_length]

/-- **Faithfulness realized.** The pump delivers the whole source stream to the
destination — a fully-discharged instance of `splice_faithful` (no residual
hypotheses), witnessing that faithfulness is non-vacuous on any real input. -/
theorem pump_faithful (stream : Bytes) :
    (runChan (freshChan stream) (pumpSchedule stream)).atDst = stream := by
  have h := pump_drains stream
  exact splice_faithful stream (pumpSchedule stream) h.1 h.2

/-- A concrete bidirectional pump: pump c2u, then pump u2c. -/
def pumpRelaySchedule (clientStream upstreamStream : Bytes) : List BiPhase :=
  [.up (.pull clientStream.length), .up (.push clientStream.length),
   .down (.pull upstreamStream.length), .down (.push upstreamStream.length)]

/-- **Both directions realized.** The bidirectional pump delivers each source
stream to its destination — a fully-discharged instance of
`splice_relay_faithful`, and it emits no userspace bytes
(`splice_no_userspace_copy`), so the two headline properties hold together on
real input. -/
theorem pump_relay_faithful (f : Fds) (clientStream upstreamStream : Bytes) :
    (runRelay (freshRelay clientStream upstreamStream)
        (pumpRelaySchedule clientStream upstreamStream)).c2u.atDst = clientStream
    ∧ (runRelay (freshRelay clientStream upstreamStream)
        (pumpRelaySchedule clientStream upstreamStream)).u2c.atDst = upstreamStream
    ∧ userspaceBytes (emitAll f (pumpRelaySchedule clientStream upstreamStream)) = [] := by
  refine ⟨?_, ?_, splice_no_userspace_copy f _⟩
  · rw [runRelay_c2u]
    have : projUp (pumpRelaySchedule clientStream upstreamStream) = pumpSchedule clientStream := by
      simp [pumpRelaySchedule, projUp, projDown, pumpSchedule]
    rw [this]; exact pump_faithful clientStream
  · rw [runRelay_u2c]
    have : projDown (pumpRelaySchedule clientStream upstreamStream)
             = pumpSchedule upstreamStream := by
      simp [pumpRelaySchedule, projUp, projDown, pumpSchedule]
    rw [this]; exact pump_faithful upstreamStream

/-- A concrete non-trivial witness on real bytes: five bytes spliced through in
two-byte chunks, both directions, arriving verbatim. `decide` computes it —
grounding the model in an executable run, no `native_decide`. -/
example :
    (runRelay (freshRelay [1, 2, 3, 4, 5] [9, 8, 7])
        [.up (.pull 2), .up (.push 2), .up (.pull 2), .up (.push 2),
         .up (.pull 2), .up (.push 2),
         .down (.pull 3), .down (.push 3)]).c2u.atDst = [1, 2, 3, 4, 5]
    ∧ (runRelay (freshRelay [1, 2, 3, 4, 5] [9, 8, 7])
        [.up (.pull 2), .up (.push 2), .up (.pull 2), .up (.push 2),
         .up (.pull 2), .up (.push 2),
         .down (.pull 3), .down (.push 3)]).u2c.atDst = [9, 8, 7] := by
  decide

/-! ## The DEPLOYED schedule: the chunked lockstep fill/drain loop

`pumpSchedule` is a single whole-stream pull then a single whole-stream push —
one giant splice each way. The running datapath cannot issue that: a kernel pipe
has bounded capacity, so `crates/dataplane/src/l4.rs`'s `splice_to_eof`
(`kernel_splice.Relay.move_to_eof`) fills the pipe with at most `SPLICE_CHUNK`
(64 KiB) bytes, drains exactly that many to the destination, then repeats until
the source returns `0` (EOF) — a *lockstep chunked* schedule
`pull c ; push c ; pull c ; push c ; …`, one iteration per kernel `splice` fill.

This section models that exact loop (`drainLoop`) and proves it byte-transparent:
for any positive chunk and enough iterations it drains (source at EOF, pipe
empty) and delivers the whole source verbatim. So the schedule the host actually
runs is itself proven faithful — not merely one of the schedules `splice_faithful`
quantifies over. The bound is discharged with `fuel = stream.length`, which is
always enough for a chunk of at least one byte, so the deployed corollary carries
no side condition beyond a positive chunk. -/

/-- Left-fold structure of a run: running `xs ++ ys` is running `ys` from the
state `xs` leaves. -/
theorem runChan_append (c : Chan) (xs ys : List Phase) :
    runChan c (xs ++ ys) = runChan (runChan c xs) ys := by
  induction xs generalizing c with
  | nil => rfl
  | cons x xs ih => simp [runChan, ih]

/-- The deployed fill/drain loop as a phase schedule: `fuel` iterations, each a
`pull chunk` (socket -> pipe, up to `chunk` bytes) immediately followed by a
`push chunk` (pipe -> socket) draining exactly what the fill produced — one
iteration per `Relay.move_to_eof` `splice`-fill-then-`drain`. -/
def drainLoop (chunk : Nat) : Nat -> List Phase
  | 0        => []
  | fuel + 1 => .pull chunk :: .push chunk :: drainLoop chunk fuel

/-- One fill/drain pair on a channel whose pipe is empty moves the next `chunk`
bytes from source to destination and leaves the pipe empty again: the fill
buffers `take chunk atSrc`; the drain flushes exactly those (the pipe never holds
more than one fill, so `push chunk` empties it). -/
theorem runChan_fillDrain (c : Chan) (chunk : Nat) (h : c.inPipe = []) :
    runChan c [.pull chunk, .push chunk]
      = ⟨c.atSrc.drop chunk, [], c.atDst ++ c.atSrc.take chunk⟩ := by
  have hdrop : (c.atSrc.take chunk).drop chunk = [] :=
    List.drop_eq_nil_iff.mpr (List.length_take_le chunk c.atSrc)
  simp only [runChan, stepChan, pull, push, h, List.nil_append,
             List.take_take, Nat.min_self, hdrop]

/-- **The whole chunked loop, unrolled.** After `fuel` fill/drain iterations from
a fresh-pipe channel, the source has advanced by `chunk * fuel`, the pipe is
empty, and the destination has received exactly those first `chunk * fuel`
source bytes, in order. -/
theorem runChan_drainLoop (s d : Bytes) (chunk fuel : Nat) :
    runChan ⟨s, [], d⟩ (drainLoop chunk fuel)
      = ⟨s.drop (chunk * fuel), [], d ++ s.take (chunk * fuel)⟩ := by
  induction fuel generalizing s d with
  | zero => simp [drainLoop, runChan, Nat.mul_zero]
  | succ fuel ih =>
    show runChan ⟨s, [], d⟩ ([.pull chunk, .push chunk] ++ drainLoop chunk fuel) = _
    rw [runChan_append, runChan_fillDrain ⟨s, [], d⟩ chunk rfl,
        ih (s.drop chunk) (d ++ s.take chunk)]
    congr 1
    · rw [List.drop_drop, Nat.mul_succ, Nat.add_comm chunk (chunk * fuel)]
    · rw [List.append_assoc, ← List.take_add, Nat.mul_succ,
          Nat.add_comm chunk (chunk * fuel)]

/-- A fresh channel for `stream` under the deployed schedule with `fuel`
iterations drains exactly when `fuel` fills cover the stream. -/
theorem drainLoop_drains (stream : Bytes) (chunk fuel : Nat)
    (hf : stream.length ≤ chunk * fuel) :
    (runChan (freshChan stream) (drainLoop chunk fuel)).inPipe = []
    ∧ (runChan (freshChan stream) (drainLoop chunk fuel)).atSrc = [] := by
  rw [freshChan, runChan_drainLoop]
  exact ⟨rfl, List.drop_eq_nil_iff.mpr hf⟩

/-- **The deployed chunked splice loop is byte-transparent (one direction).**
With a positive chunk (the real `SPLICE_CHUNK` is 64 KiB) and `fuel = stream.length`
iterations — always enough — the destination fd receives exactly the source
stream, verbatim and in order, and the loop has drained (source at EOF, pipe
empty). This is the byte semantics of one `kernel_splice.Relay.move_to_eof` call:
the running host's per-direction pump, proven identity, not asserted. -/
theorem deployed_splice_faithful (stream : Bytes) (chunk : Nat) (hc : 0 < chunk) :
    (runChan (freshChan stream) (drainLoop chunk stream.length)).atDst = stream
    ∧ (runChan (freshChan stream) (drainLoop chunk stream.length)).inPipe = []
    ∧ (runChan (freshChan stream) (drainLoop chunk stream.length)).atSrc = [] := by
  have hf : stream.length ≤ chunk * stream.length := Nat.le_mul_of_pos_left stream.length hc
  have hd := drainLoop_drains stream chunk stream.length hf
  exact ⟨splice_faithful stream (drainLoop chunk stream.length) hd.1 hd.2, hd.1, hd.2⟩

/-! ## Both directions under the deployed loop

The whole L4 connection runs one `move_to_eof` per direction (`l4.rs`'s
`splice` spawns the client->upstream pump on a helper thread and runs
upstream->client on the connection thread). Tagging each direction's chunked
loop and concatenating gives the connection's BiPhase schedule; the two
directions are independent (`runRelay_c2u` / `runRelay_u2c`), so each drains and
is faithful on its own stream. -/

theorem projUp_map_up (ps : List Phase) : projUp (ps.map .up) = ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [projUp, ih]

theorem projUp_map_down (ps : List Phase) : projUp (ps.map .down) = [] := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [projUp, ih]

theorem projDown_map_down (ps : List Phase) : projDown (ps.map .down) = ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [projDown, ih]

theorem projDown_map_up (ps : List Phase) : projDown (ps.map .up) = [] := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [projDown, ih]

theorem projUp_append (xs ys : List BiPhase) :
    projUp (xs ++ ys) = projUp xs ++ projUp ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [projUp, ih]

theorem projDown_append (xs ys : List BiPhase) :
    projDown (xs ++ ys) = projDown xs ++ projDown ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [projDown, ih]

/-- The connection's deployed BiPhase schedule: the client->upstream chunked
loop tagged `up`, then the upstream->client chunked loop tagged `down`. -/
def deployedRelaySchedule (chunk : Nat) (clientStream upstreamStream : Bytes) : List BiPhase :=
  (drainLoop chunk clientStream.length).map .up
    ++ (drainLoop chunk upstreamStream.length).map .down

/-- **The deployed L4 relay is byte-transparent in both directions.** Under the
exact chunked lockstep schedule the running host issues (one `splice`-fill/drain
loop per direction, positive `SPLICE_CHUNK`), the client->upstream destination
receives the client's stream verbatim and the upstream->client destination
receives the upstream's stream verbatim — every byte, in order, nothing
dropped, reordered, or invented. The deployed schedule is exhibited, and it is
faithful. -/
theorem deployed_relay_faithful (chunk : Nat) (clientStream upstreamStream : Bytes)
    (hc : 0 < chunk) :
    (runRelay (freshRelay clientStream upstreamStream)
        (deployedRelaySchedule chunk clientStream upstreamStream)).c2u.atDst = clientStream
    ∧ (runRelay (freshRelay clientStream upstreamStream)
        (deployedRelaySchedule chunk clientStream upstreamStream)).u2c.atDst = upstreamStream := by
  have hup : projUp (deployedRelaySchedule chunk clientStream upstreamStream)
      = drainLoop chunk clientStream.length := by
    simp [deployedRelaySchedule, projUp_append, projUp_map_up, projUp_map_down]
  have hdown : projDown (deployedRelaySchedule chunk clientStream upstreamStream)
      = drainLoop chunk upstreamStream.length := by
    simp [deployedRelaySchedule, projDown_append, projDown_map_down, projDown_map_up]
  refine ⟨?_, ?_⟩
  · rw [runRelay_c2u, freshRelay, hup]
    exact (deployed_splice_faithful clientStream chunk hc).1
  · rw [runRelay_u2c, freshRelay, hdown]
    exact (deployed_splice_faithful upstreamStream chunk hc).1

/-- A concrete multi-fill run, mirroring the strace of the running host: a
5-byte stream through a 2-byte chunk needs three fill/drain iterations and
arrives verbatim; `decide` computes the whole schedule, grounding the deployed
loop in an executable run (no `native_decide`). -/
example :
    (runChan (freshChan [1, 2, 3, 4, 5]) (drainLoop 2 5)).atDst = [1, 2, 3, 4, 5]
      ∧ (runChan (freshChan [1, 2, 3, 4, 5]) (drainLoop 2 5)).atSrc = []
      ∧ (runChan (freshChan [1, 2, 3, 4, 5]) (drainLoop 2 5)).inPipe = [] := by decide


end L4.Splice
