import Ws.Reassembly

/-!
# The reassembly admission verdict (RFC 6455 §5.4, §7.4.1/1009) — in the core

`Ws.Reassembly` proves the fragmentation state machine: which frame sequences
form a message, that control frames interleave transparently, and that a
delivered message is the in-order concatenation of its fragments. The host's
message engine enforces exactly that discipline — plus the bounded-memory
admission (one reassembly buffer, hard-capped, with an over-declared frame
refused by close 1009 *before* any of its payload is buffered) — at header
time. Until now that decision lived only in the host.

This module lifts it into the core. `admit` is a **total** function (no
recursion — the decision is a finite case split) from the host's
between-frames state (`OpenMsg` — is a data message open, and with which
opcode), the number of bytes already buffered, and the arriving frame's
header fields, to one of:

* `reject 1002` — a §5.4 discipline violation (a continuation with no message
  open; a fresh data opcode preempting an open message; a reserved opcode);
* `reject 1009` — the frame's declared length would push the reassembled
  message over the cap (§7.4.1: refused before buffering);
* `accept during after deliver` — admitted: `during` is the message opcode
  while this frame's payload streams in, `after` the state once the frame
  completes, `deliver` whether completion delivers a message.

The theorems:

* `admit_control` — control frames are admitted with the reassembly state
  untouched (§5.5 interleaving), matching `Reassembly.step_control_state`.
* `reject_protocol_iff_step_error` — **the 1002 verdict is the proven FSM's
  error, exactly**: for a data frame, `admit` answers `reject 1002` iff
  `Reassembly.step` answers `error` from the corresponding state.
* `accept_matches_step` — **an accepted frame drives the proven FSM**: the
  verdict's `during`/`after`/`deliver` and the host's byte concatenation are
  exactly `Reassembly.step`'s transition — delivery on `fin` of the in-order
  accumulated payload (`assemble_join` semantics), absorption otherwise.
* `accept_within_cap` / `over_cap_rejected_*` — **the bound is enforced and
  exact**: an accepted data frame keeps `buffered + declared ≤ cap`, and a
  discipline-clean data frame over the cap is refused with 1009.
* Kernel-checked vectors at the 16 MiB deployment cap.

`drorb_ws_admit` (`@[export]`) is the C-ABI seam: scalar fields in, packed
verdict out. The host keeps only the byte buffering; every admission verdict
and every `msg_op` state transition it applies is this module's.
-/

namespace Ws
namespace ReassemblyAdmit

/-! ## The host's between-frames state and the verdict -/

/-- The host's between-frames data-message state: no message open, or a
text/binary message open awaiting continuations. (The host stores this as its
`msg_op` byte: `0`/`0x1`/`0x2` — the wire codes below.) -/
inductive OpenMsg where
  | idle
  | text
  | binary
deriving Repr, DecidableEq

/-- The data opcode of an open message. -/
def OpenMsg.opcode? : OpenMsg → Option Opcode
  | .idle => none
  | .text => some .text
  | .binary => some .binary

/-- The header-time admission verdict. -/
inductive Verdict where
  /-- Admitted. `during`: the message opcode while this frame's payload
  streams; `after`: the state once the frame completes; `deliver`: completion
  delivers a message. -/
  | accept (during after : OpenMsg) (deliver : Bool)
  /-- Fail the connection with this close code before buffering anything. -/
  | reject (code : Nat)
deriving Repr, DecidableEq

/-- **The admission verdict** (RFC 6455 §5.4 + the §7.4.1/1009 bound),
decided at header time — before any payload byte is buffered. In the host's
check order: control frames pass untouched; then the fragmentation
discipline; then the reassembly bound `buffered + declared ≤ cap`. -/
def admit (cap : Nat) (m : OpenMsg) (bufLen : Nat) (op : Opcode) (fin : Bool)
    (len : Nat) : Verdict :=
  if op.isControl then .accept m m false
  else
    match op with
    | .continuation =>
      match m with
      | .idle => .reject closeProtocolError  -- nothing to continue (§5.4)
      | _ =>
        if cap < bufLen + len then .reject closeTooBig
        else .accept m (if fin then .idle else m) fin
    | .text =>
      match m with
      | .idle =>
        if cap < bufLen + len then .reject closeTooBig
        else .accept .text (if fin then .idle else .text) fin
      | _ => .reject closeProtocolError  -- data frame preempts an open message
    | .binary =>
      match m with
      | .idle =>
        if cap < bufLen + len then .reject closeTooBig
        else .accept .binary (if fin then .idle else .binary) fin
      | _ => .reject closeProtocolError
    | _ => .reject closeProtocolError  -- reserved opcode (already refused at decode)

/-- The `Reassembly` state an `OpenMsg` + accumulated bytes denote. -/
def stateOf (m : OpenMsg) (acc : Bytes) : Reassembly.State :=
  match m with
  | .idle => .idle
  | .text => .assembling { opcode := .text, acc := acc }
  | .binary => .assembling { opcode := .binary, acc := acc }

/-! ## Control transparency (§5.5) -/

/-- A control frame is admitted with the reassembly state untouched and no
delivery — the header-time half of `Reassembly.step_control_state`. -/
theorem admit_control (cap : Nat) (m : OpenMsg) (bufLen : Nat) (op : Opcode)
    (fin : Bool) (len : Nat) (h : op.isControl = true) :
    admit cap m bufLen op fin len = .accept m m false := by
  simp [admit, h]

/-! ## The 1002 verdict is the proven FSM's error, exactly -/

/-- **Discipline agreement.** For a data frame, `admit` answers
`reject 1002` iff the proven fragmentation FSM answers `error` from the
corresponding state — the header-time verdict and `Reassembly.step` refuse
exactly the same frames (the cap refusal is 1009, not 1002, and accepted
frames are not FSM errors). -/
theorem reject_protocol_iff_step_error (cap : Nat) (m : OpenMsg)
    (bufLen : Nat) (f : Frame) (acc : Bytes) (hdata : f.opcode.isData = true) :
    admit cap m bufLen f.opcode f.fin f.payload.length
        = .reject closeProtocolError
      ↔ (Reassembly.step (stateOf m acc) f).2 = .error := by
  obtain ⟨fin, op, pl⟩ := f
  cases op <;> simp only [Opcode.isData, Bool.false_eq_true] at hdata <;> cases m <;>
    simp only [admit, Reassembly.step, stateOf, Opcode.isControl,
               Bool.false_eq_true, reduceIte]
  -- (the four discipline-error arms close by the simp: both sides refuse)
  -- the accepted (or cap-refused) arms: neither side is a 1002/error
  case mk.continuation.text =>
    constructor
    · intro hr
      split at hr
      · exact absurd (Verdict.reject.inj hr) (by decide)
      · exact Verdict.noConfusion hr
    · intro hs
      exfalso
      revert hs
      cases fin <;> simp
  case mk.continuation.binary =>
    constructor
    · intro hr
      split at hr
      · exact absurd (Verdict.reject.inj hr) (by decide)
      · exact Verdict.noConfusion hr
    · intro hs
      exfalso
      revert hs
      cases fin <;> simp
  case mk.text.idle =>
    constructor
    · intro hr
      split at hr
      · exact absurd (Verdict.reject.inj hr) (by decide)
      · exact Verdict.noConfusion hr
    · intro hs
      exfalso
      revert hs
      cases fin <;> simp
  case mk.binary.idle =>
    constructor
    · intro hr
      split at hr
      · exact absurd (Verdict.reject.inj hr) (by decide)
      · exact Verdict.noConfusion hr
    · intro hs
      exfalso
      revert hs
      cases fin <;> simp

/-! ## An accepted frame drives the proven FSM -/

/-- **Transition agreement.** An accepted data frame's verdict fields are
exactly the proven FSM's transition: `deliver` is FIN, `after` is idle
exactly on delivery, and `Reassembly.step` from the corresponding state
delivers (on FIN) the message with opcode `during` and payload
`acc ++ f.payload` — the in-order concatenation the host's buffering
implements (`Reassembly.assemble_join` fixes its semantics) — or absorbs the
frame into `⟨during, acc ++ f.payload⟩`. `hidle` is the host invariant that
the buffer is empty between messages. -/
theorem accept_matches_step (cap : Nat) (m : OpenMsg) (f : Frame)
    (acc : Bytes) (hdata : f.opcode.isData = true)
    (hidle : m = .idle → acc = [])
    {during after : OpenMsg} {deliver : Bool}
    (h : admit cap m acc.length f.opcode f.fin f.payload.length
          = .accept during after deliver) :
    deliver = f.fin
    ∧ after = (if f.fin then .idle else during)
    ∧ ∃ op, during.opcode? = some op
        ∧ Reassembly.step (stateOf m acc) f
            = if f.fin then (.idle, .message op (acc ++ f.payload))
              else (.assembling { opcode := op, acc := acc ++ f.payload },
                    .absorbed) := by
  obtain ⟨fin, op, pl⟩ := f
  cases op <;> simp only [Opcode.isData, Bool.false_eq_true] at hdata <;> cases m <;>
    simp only [admit, Opcode.isControl, Bool.false_eq_true, reduceIte] at h
  -- continuation / idle: discipline-rejected
  case mk.continuation.idle => exact Verdict.noConfusion h
  -- text, binary / open message: discipline-rejected
  case mk.text.text => exact Verdict.noConfusion h
  case mk.text.binary => exact Verdict.noConfusion h
  case mk.binary.text => exact Verdict.noConfusion h
  case mk.binary.binary => exact Verdict.noConfusion h
  -- the accepted arms: cap-split, then the FSM computes
  case mk.continuation.text =>
    split at h
    · exact Verdict.noConfusion h
    · injection h with h1 h2 h3
      subst h1; subst h2; subst h3
      exact ⟨rfl, rfl, .text, rfl, by
        cases fin <;> simp [Reassembly.step, stateOf, Opcode.isControl]⟩
  case mk.continuation.binary =>
    split at h
    · exact Verdict.noConfusion h
    · injection h with h1 h2 h3
      subst h1; subst h2; subst h3
      exact ⟨rfl, rfl, .binary, rfl, by
        cases fin <;> simp [Reassembly.step, stateOf, Opcode.isControl]⟩
  case mk.text.idle =>
    have hacc := hidle rfl
    subst hacc
    split at h
    · exact Verdict.noConfusion h
    · injection h with h1 h2 h3
      subst h1; subst h2; subst h3
      exact ⟨rfl, rfl, .text, rfl, by
        cases fin <;> simp [Reassembly.step, stateOf, Opcode.isControl]⟩
  case mk.binary.idle =>
    have hacc := hidle rfl
    subst hacc
    split at h
    · exact Verdict.noConfusion h
    · injection h with h1 h2 h3
      subst h1; subst h2; subst h3
      exact ⟨rfl, rfl, .binary, rfl, by
        cases fin <;> simp [Reassembly.step, stateOf, Opcode.isControl]⟩

/-! ## The bound is enforced and exact -/

/-- **The cap holds.** An accepted data frame keeps the reassembled size
within the cap: `buffered + declared ≤ cap`. Applied per frame, the host's
reassembly buffer can never exceed `cap` — the declared length is checked
before any byte of it is buffered. -/
theorem accept_within_cap {cap : Nat} {m : OpenMsg} {bufLen : Nat}
    {op : Opcode} {fin : Bool} {len : Nat} {during after : OpenMsg}
    {deliver : Bool} (hdata : op.isData = true)
    (h : admit cap m bufLen op fin len = .accept during after deliver) :
    bufLen + len ≤ cap := by
  cases op <;> simp only [Opcode.isData, Bool.false_eq_true] at hdata <;> cases m <;>
    simp only [admit, Opcode.isControl, Bool.false_eq_true, reduceIte] at h <;>
    first
    | exact Verdict.noConfusion h
    | (by_cases hc : cap < bufLen + len
       · rw [if_pos hc] at h; exact Verdict.noConfusion h
       · omega)

/-- **The 1009 refusal is exact (opening frame).** A discipline-clean opening
data frame whose declared length overruns the cap is refused with 1009. -/
theorem over_cap_rejected_first (cap : Nat) (bufLen : Nat) (fin : Bool)
    (len : Nat) (op : Opcode) (hop : op = .text ∨ op = .binary)
    (hover : cap < bufLen + len) :
    admit cap .idle bufLen op fin len = .reject closeTooBig := by
  rcases hop with h | h <;> subst h <;>
    simp [admit, Opcode.isControl, hover]

/-- **The 1009 refusal is exact (continuation).** A continuation of an open
message whose declared length would push the reassembled size over the cap is
refused with 1009. -/
theorem over_cap_rejected_cont (cap : Nat) (m : OpenMsg) (bufLen : Nat)
    (fin : Bool) (len : Nat) (hm : ¬ m = .idle)
    (hover : cap < bufLen + len) :
    admit cap m bufLen .continuation fin len = .reject closeTooBig := by
  cases m
  · exact absurd rfl hm
  all_goals simp [admit, Opcode.isControl, hover]

/-! ## Kernel-checked vectors at the deployment cap (non-vacuity) -/

/-- The deployed reassembly cap: 16 MiB. -/
def deployedCap : Nat := 16 * 1024 * 1024

/-- An unfragmented text frame opens and delivers. -/
theorem vec_text_delivers :
    admit deployedCap .idle 0 .text true 5 = .accept .text .idle true := by
  decide

/-- A non-final binary frame opens a fragmented message. -/
theorem vec_binary_opens :
    admit deployedCap .idle 0 .binary false 5
      = .accept .binary .binary false := by decide

/-- A final continuation delivers and returns to idle. -/
theorem vec_cont_delivers :
    admit deployedCap .text 10 .continuation true 5
      = .accept .text .idle true := by decide

/-- §5.4: a continuation with no message open is a protocol error. -/
theorem vec_cont_idle_refused :
    admit deployedCap .idle 0 .continuation true 0
      = .reject closeProtocolError := by decide

/-- §5.4: a fresh text frame preempting an open message is a protocol
error. -/
theorem vec_preempt_refused :
    admit deployedCap .text 4 .text true 1 = .reject closeProtocolError := by
  decide

/-- §5.5: a ping between fragments passes with the state untouched. -/
theorem vec_ping_transparent :
    admit deployedCap .text 10 .ping true 5 = .accept .text .text false := by
  decide

/-- §7.4.1: one byte over the cap is refused with 1009 — at the exact
boundary, and before buffering. -/
theorem vec_cap_boundary :
    admit deployedCap .idle 0 .binary true deployedCap
        = .accept .binary .idle true
      ∧ admit deployedCap .idle 0 .binary true (deployedCap + 1)
        = .reject closeTooBig
      ∧ admit deployedCap .binary 1 .continuation false deployedCap
        = .reject closeTooBig := by decide

/-! ## The host-facing C-ABI seam -/

/-- The wire code of the between-frames state (the host's `msg_op` byte:
idle `0`, text `0x1`, binary `0x2` — the RFC opcode nibbles). -/
def OpenMsg.code : OpenMsg → UInt64
  | .idle => 0
  | .text => 1
  | .binary => 2

/-- Decode a wire state code. -/
def ofCode (c : UInt32) : Option OpenMsg :=
  if c = 0 then some .idle
  else if c = 1 then some .text
  else if c = 2 then some .binary
  else none

/-- The state encoding round-trips (the host echoes `during`/`after` codes
back as the next call's state). -/
theorem ofCode_code :
    ofCode 0 = some .idle ∧ ofCode 1 = some .text ∧ ofCode 2 = some .binary
      ∧ (OpenMsg.code .idle = 0 ∧ OpenMsg.code .text = 1
          ∧ OpenMsg.code .binary = 2) := by decide

/-- **`drorb_ws_admit`.** The seam the host's message engine crosses instead
of deciding admission itself: the between-frames state, buffered length, and
header fields in; the packed verdict out. High 32 bits: `1` = reject (low 16
bits the close code), `2` = accept (bits 8–11 `during`, bits 4–7 `after`,
bit 0 `deliver`). An out-of-range state code (which the host never sends — it
only ever stores this function's own `during`/`after` output) rejects 1002. -/
@[export drorb_ws_admit]
def admitExport (m : UInt32) (bufLen : UInt64) (opcode : UInt32) (fin : UInt8)
    (len : UInt64) (cap : UInt64) : UInt64 :=
  match ofCode m with
  | none => ((1 : UInt64) <<< 32) ||| UInt64.ofNat closeProtocolError
  | some mm =>
    match admit cap.toNat mm bufLen.toNat (Opcode.ofNat opcode.toNat)
        (fin != 0) len.toNat with
    | .reject code => ((1 : UInt64) <<< 32) ||| UInt64.ofNat code
    | .accept during after deliver =>
      ((2 : UInt64) <<< 32) ||| (during.code <<< 8) ||| (after.code <<< 4)
        ||| (if deliver then (1 : UInt64) else 0)

/-- **ABI vectors.** The packed encodings, octet-exact: an accepted opening
text frame (`during` text, `after` text, no delivery), a delivered final
continuation, a 1002 refusal, and a 1009 refusal at the 16 MiB cap. -/
theorem vec_abi :
    admitExport 0 0 1 0 5 16777216
        = ((2 : UInt64) <<< 32) ||| ((1 : UInt64) <<< 8) ||| ((1 : UInt64) <<< 4)
    ∧ admitExport 1 10 0 1 5 16777216
        = ((2 : UInt64) <<< 32) ||| ((1 : UInt64) <<< 8) ||| 1
    ∧ admitExport 0 0 0 1 0 16777216 = ((1 : UInt64) <<< 32) ||| 1002
    ∧ admitExport 0 0 2 1 16777217 16777216
        = ((1 : UInt64) <<< 32) ||| 1009 := by
  decide

end ReassemblyAdmit
end Ws
