import H2.Frame
import H2.Stream

/-!
# HTTP/2 RST_STREAM — abrupt cancellation and the rapid-reset defence

The **RST_STREAM** frame (type `0x3`) requests immediate termination of a single
stream (RFC 9113 §6.4). Its payload is a fixed **4-octet error code** naming the
reason for the reset; any other payload length is a `FRAME_SIZE_ERROR`, and a
RST_STREAM on stream `0x0` is a connection `PROTOCOL_ERROR`.

This module sits on top of two lower layers:

* the frame layer (`H2/Frame.lean`) — `H2.decode` recognises a RST_STREAM frame
  (`Frame.rstStream`) and hands the raw 4-octet payload to `parseRstStream` here;
* the per-stream FSM (`H2/Stream.lean`) — an accepted reset drives the
  `recvRstStream` event, which the state machine already sends to the absorbing
  `closed` state from every live state.

Headline results:

* `h2_rst_error_code` — every 4-octet payload parses to a 32-bit big-endian error
  code, and a reset on a non-zero stream is accepted carrying exactly that code.
  A payload of any length other than 4 is `FRAME_SIZE_ERROR`; a reset on stream 0
  is `PROTOCOL_ERROR`.
* `h2_rst_cancels` — an accepted RST_STREAM moves the stream to `closed`, and from
  there **no further frames are processed on it**: under any subsequent
  interleaving of events the stream stays `closed` and later DATA is refused
  (`STREAM_CLOSED`). This is the RFC 9113 §6.4 cancellation guarantee, lifted
  from `H2.Stream`'s absorbing-`closed` invariant.
* `h2_rapid_reset_bounded` — the CVE-2023-44487 ("HTTP/2 Rapid Reset") defence: a
  connection admits at most a fixed budget of resets before it refuses further
  ones with `ENHANCE_YOUR_CALM`. No matter how long a flood of open+RST cycles
  runs, the count of *accepted* resets never exceeds the budget (`flood_bounded`),
  and once the budget is spent every further reset is refused
  (`admit_refuses_when_full`).

There is no cryptography on this path: RST_STREAM carries an integer error code
only, so nothing here is an opaque oracle. All results are structural.
-/

namespace H2
namespace RstStream

/-! ## Error codes (RFC 9113 §7) -/

/-- `NO_ERROR` — graceful shutdown (RFC 9113 §7). -/
def errNoError : Nat := 0x0
/-- `PROTOCOL_ERROR` (RFC 9113 §7). -/
def errProtocolError : Nat := 0x1
/-- `REFUSED_STREAM` — stream not processed; the client may safely retry. -/
def errRefusedStream : Nat := 0x7
/-- `CANCEL` — the stream is no longer needed (RFC 9113 §7). -/
def errCancel : Nat := 0x8
/-- `ENHANCE_YOUR_CALM` — the peer is generating excessive load; the
rapid-reset refusal code (RFC 9113 §7). -/
def errEnhanceYourCalm : Nat := 0xb

/-! ## The 4-octet RST_STREAM payload -/

/-- A parsed RST_STREAM signal: the stream it targets and the 32-bit error code
naming the reason for the reset (RFC 9113 §6.4). -/
structure RstFields where
  /-- The stream being reset. -/
  streamId : Nat
  /-- The 32-bit error code (RFC 9113 §7). -/
  errorCode : Nat
deriving Repr, DecidableEq

/-- Outcome of accepting a RST_STREAM frame. `frameSizeError` is a payload whose
length is not exactly 4 octets; `protocolError` is a reset on stream `0x0`
(RFC 9113 §6.4). -/
inductive RstResult where
  | ok (r : RstFields)
  | frameSizeError
  | protocolError
deriving Repr, DecidableEq

/-- Parse the 4-octet RST_STREAM payload (RFC 9113 §6.4) into its big-endian
error code. Any other length is `none` (the caller raises `FRAME_SIZE_ERROR`). -/
def parseRstStream : Bytes → Option Nat
  | [e0, e1, e2, e3] =>
    some (e0.toNat * 2 ^ 24 + e1.toNat * 2 ^ 16 + e2.toNat * 2 ^ 8 + e3.toNat)
  | _ => none

/-- Accept a RST_STREAM received on stream `streamId` with raw `payload`
(RFC 9113 §6.4): the length check, then the stream-0 protocol check, then a
well-formed signal carrying the parsed error code. -/
def validate (streamId : Nat) (payload : Bytes) : RstResult :=
  match parseRstStream payload with
  | none => .frameSizeError
  | some code =>
    if streamId = 0 then .protocolError
    else .ok { streamId := streamId, errorCode := code }

/-! ## `h2_rst_error_code` — the 4-octet error code -/

/-- **RST_STREAM carries a 32-bit error code** (RFC 9113 §6.4, §7): every
4-octet payload parses to the big-endian composition of its four octets, which
is a 32-bit value, and a reset on a non-zero stream is accepted carrying exactly
that code on that stream. -/
theorem h2_rst_error_code (streamId : Nat) (e0 e1 e2 e3 : UInt8) (hnz : streamId ≠ 0) :
    ∃ code, parseRstStream [e0, e1, e2, e3] = some code ∧
      code = e0.toNat * 2 ^ 24 + e1.toNat * 2 ^ 16 + e2.toNat * 2 ^ 8 + e3.toNat ∧
      code < 2 ^ 32 ∧
      validate streamId [e0, e1, e2, e3] = .ok { streamId := streamId, errorCode := code } := by
  refine ⟨_, rfl, rfl, ?_, ?_⟩
  · have h0 := u8_toNat_lt e0
    have h1 := u8_toNat_lt e1
    have h2 := u8_toNat_lt e2
    have h3 := u8_toNat_lt e3
    omega
  · simp only [validate, parseRstStream]
    rw [if_neg hnz]

/-- **Length check** (RFC 9113 §6.4): a RST_STREAM payload of any length other
than 4 octets is a `FRAME_SIZE_ERROR`. -/
theorem h2_rst_frame_size (streamId : Nat) (payload : Bytes) (h : payload.length ≠ 4) :
    validate streamId payload = .frameSizeError := by
  have hp : parseRstStream payload = none := by
    rcases payload with _|⟨a,_|⟨b,_|⟨c,_|⟨d,_|⟨e,rest⟩⟩⟩⟩⟩ <;> simp_all [parseRstStream]
  simp only [validate, hp]

/-- **Stream-0 rejection** (RFC 9113 §6.4): a RST_STREAM on stream `0x0` is a
connection `PROTOCOL_ERROR`, whatever error code its 4-octet payload names. -/
theorem h2_rst_stream0 (e0 e1 e2 e3 : UInt8) :
    validate 0 [e0, e1, e2, e3] = .protocolError := by
  simp [validate, parseRstStream]

/-! ## `h2_rst_cancels` — cancellation is absorbing -/

/-- The states from which a received RST_STREAM is *accepted* and closes the
stream: every state except `idle` (a reset on an idle stream is a
`PROTOCOL_ERROR`, so there is nothing to cancel). -/
def canReset : Stream.StreamState → Bool
  | .idle => false
  | _ => true

/-- From any resettable state, `recvRstStream` transitions to `closed`
(RFC 9113 §6.4). -/
theorem rst_step_closes (s : Stream.StreamState) (h : canReset s = true) :
    Stream.step s .recvRstStream = .next .closed := by
  cases s <;> first | rfl | exact absurd h (by decide)

/-- **RST_STREAM cancels the stream** (RFC 9113 §6.4): from any resettable state
a received RST_STREAM moves the stream to `closed`, and from there **no further
frames are processed on it** — under *any* subsequent interleaving of events the
stream stays `closed`, and any later DATA is refused with `STREAM_CLOSED`. -/
theorem h2_rst_cancels (s : Stream.StreamState) (es : List Stream.Event) (b : Bool)
    (h : canReset s = true) :
    Stream.stepState s .recvRstStream = .closed ∧
      Stream.run (Stream.stepState s .recvRstStream) es = .closed ∧
      Stream.step (Stream.run (Stream.stepState s .recvRstStream) es) (.recvData b)
        = .streamClosed := by
  have hc : Stream.stepState s .recvRstStream = .closed := by
    unfold Stream.stepState
    rw [rst_step_closes s h]
  refine ⟨hc, ?_, ?_⟩
  · rw [hc]; exact Stream.run_closed es
  · rw [hc, Stream.run_closed es]; rfl

/-! ## `h2_rapid_reset_bounded` — the CVE-2023-44487 defence

"HTTP/2 Rapid Reset" (CVE-2023-44487): a peer opens a stream and immediately
resets it, over and over, to make the server do per-request work while never
paying the concurrency cost of `MAX_CONCURRENT_STREAMS`. The defence is a
**reset budget**: the connection admits at most a fixed number of resets before
refusing further ones (in practice, closing the connection with
`ENHANCE_YOUR_CALM`). -/

/-- The reset-rate guard: how many resets have been *accepted* in the current
window, and the per-window budget (`cap`). -/
structure Guard where
  /-- Resets accepted so far this window. -/
  accepted : Nat
  /-- The per-window reset budget. -/
  cap : Nat
deriving Repr, DecidableEq

/-- Admitting one open+RST cycle: within budget it is accepted (the count
advances); at or over budget it is refused with `ENHANCE_YOUR_CALM`. -/
inductive Admit where
  | accept (g : Guard)
  | refuse (code : Nat)
deriving Repr, DecidableEq

/-- Process one incoming reset against the guard (RFC 9113 §7 / CVE-2023-44487):
accept iff strictly under budget, else refuse with `ENHANCE_YOUR_CALM`. -/
def admit (g : Guard) : Admit :=
  if g.accepted < g.cap then .accept { g with accepted := g.accepted + 1 }
  else .refuse errEnhanceYourCalm

/-- Fold a flood of `n` back-to-back open+RST cycles through the guard. Once a
reset is refused the connection stops admitting, so the accepted count freezes. -/
def flood (g : Guard) : Nat → Guard
  | 0 => g
  | n + 1 =>
    match admit g with
    | .accept g' => flood g' n
    | .refuse _ => g

/-- Each admission raises the accepted count by exactly one, and never past the
budget: an accepted reset came from strictly under budget. -/
theorem admit_accept_bounded (g g' : Guard) (h : admit g = .accept g') :
    g'.accepted = g.accepted + 1 ∧ g.accepted < g.cap ∧ g'.cap = g.cap := by
  unfold admit at h
  split at h
  · rename_i hlt
    cases h
    exact ⟨rfl, hlt, rfl⟩
  · exact absurd h (by simp)

/-- **The budget is spent ⇒ every reset is refused** (the liveness half of the
defence): once the accepted count reaches the budget, `admit` refuses with
`ENHANCE_YOUR_CALM`. -/
theorem admit_refuses_when_full (g : Guard) (h : g.cap ≤ g.accepted) :
    admit g = .refuse errEnhanceYourCalm := by
  unfold admit
  rw [if_neg (by omega)]

/-- The flood never lowers the budget `cap` (it is a fixed configuration). -/
theorem flood_cap (g : Guard) (n : Nat) : (flood g n).cap = g.cap := by
  induction n generalizing g with
  | zero => rfl
  | succ n ih =>
    unfold flood
    cases hA : admit g with
    | accept g' =>
      have := admit_accept_bounded g g' hA
      rw [ih g']; omega
    | refuse c => rfl

/-- **Rapid-reset is bounded** (CVE-2023-44487 defence, safety half): starting
from a guard within budget, *no matter how long* the flood runs, the number of
accepted resets never exceeds the budget. The bound is independent of the flood
length `n`. -/
theorem flood_bounded (g : Guard) (n : Nat) (h : g.accepted ≤ g.cap) :
    (flood g n).accepted ≤ g.cap := by
  induction n generalizing g with
  | zero => simpa [flood] using h
  | succ n ih =>
    unfold flood
    cases hA : admit g with
    | accept g' =>
      obtain ⟨hcnt, hlt, hcap⟩ := admit_accept_bounded g g' hA
      have hg' : g'.accepted ≤ g'.cap := by omega
      have := ih g' hg'
      rw [hcap] at this
      exact this
    | refuse c => exact h

/-- **Rapid-reset stays bounded by the original budget**: rephrasing
`flood_bounded` against the *pre-flood* cap, since the flood never changes it. -/
theorem h2_rapid_reset_bounded (g : Guard) (n : Nat) (h : g.accepted ≤ g.cap) :
    (flood g n).accepted ≤ g.cap ∧ (flood g n).cap = g.cap :=
  ⟨flood_bounded g n h, flood_cap g n⟩

/-! ## Non-vacuity witnesses -/

/-- `h2_rst_cancels`' hypothesis is inhabited: `open` is resettable, so a real
open stream is cancelled by RST_STREAM (not a vacuous claim). -/
example : canReset .open = true := rfl

/-- A fresh guard (budget 3) is within budget, so `h2_rapid_reset_bounded`'s
hypothesis holds — the theorem is not vacuous. -/
example : (Guard.mk 0 3).accepted ≤ (Guard.mk 0 3).cap := by decide

/-- A flood of 1000 open+RST cycles against a budget-3 guard admits **exactly 3**
resets — the concrete rapid-reset defence in action (not merely `≤`). -/
example : (flood (Guard.mk 0 3) 1000).accepted = 3 := by decide

/-- Once the budget is spent, the very next reset is refused with
`ENHANCE_YOUR_CALM` (`0xb`). -/
example : admit (Guard.mk 3 3) = .refuse errEnhanceYourCalm := by decide

/-! ## Wire vectors, checker-verified -/

/-- A RST_STREAM payload naming `CANCEL` (`0x0000_0008`) on stream 1 is accepted
carrying error code 8. -/
example : validate 1 [0x00, 0x00, 0x00, 0x08]
    = .ok { streamId := 1, errorCode := 8 } := by decide

/-- The full 32-bit error-code range round-trips: `0xFFFF_FFFF` parses to
`2 ^ 32 - 1`. -/
example : parseRstStream [0xFF, 0xFF, 0xFF, 0xFF] = some (2 ^ 32 - 1) := by decide

/-- A 3-octet payload (truncated error code) is a `FRAME_SIZE_ERROR`. -/
example : validate 5 [0x00, 0x00, 0x08] = .frameSizeError := by decide

/-- A RST_STREAM on stream 0 is a `PROTOCOL_ERROR`. -/
example : validate 0 [0x00, 0x00, 0x00, 0x08] = .protocolError := by decide

/-- End-to-end through the frame layer: a RST_STREAM frame (type `0x3`) on
stream 5 with error code `CANCEL` decodes via `H2.decode` and then `validate`s
to an accepted reset carrying code 8. -/
example :
    (match H2.decode [0x00, 0x00, 0x04, 0x03, 0x00, 0x00, 0x00, 0x00, 0x05,
                      0x00, 0x00, 0x00, 0x08] 16384 with
     | .complete (.rstStream sid pl) _ => validate sid pl
     | _ => .frameSizeError)
      = .ok { streamId := 5, errorCode := 8 } := by decide

/-- End-to-end cancellation: a RST_STREAM decoded at the frame layer closes an
open stream via the per-stream FSM. -/
example : Stream.stepState .open .recvRstStream = .closed := rfl

end RstStream
end H2
