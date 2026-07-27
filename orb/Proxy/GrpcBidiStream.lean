import Proxy.GrpcFraming
import H2.FlowWindow

/-!
# Proxy.GrpcBidiStream — gRPC bidirectional streaming over HTTP/2 (rp.3)

A gRPC bidirectional-streaming RPC runs a single HTTP/2 stream in which **both**
peers send an ordered sequence of length-prefixed messages concurrently: the
client sends request messages up while the server sends response messages down,
each direction independent, each independently half-closed. `Proxy.GrpcProxy`
proved the single-direction relay (`grpc_proxy_streams` handles two adjacent
directions); this module models the *bidirectional* stream directly — an
interleaved transcript of directed frames — and proves the three properties a
faithful bidi edge must hold:

## 1. Directions interleave in order, half-close is independent (`grpc_bidi_interleave`)

We model a bidi call as one interleaved transcript `List BidiEvent`: each event is
a directed message frame or a directed half-close carrying that direction's
trailer block, emitted in *some* global order (the two peers race on the wire).
Projecting the transcript onto one direction (`msgsOf`) recovers exactly that
direction's messages **in their original relative order**, and the per-direction
wire (`encodeStream` of the projection, then the trailer frame) deframes back to
that message list with the trailer frame as the untouched tail. **Independence of
half-close**: deleting every event of the *other* direction leaves a direction's
message stream unchanged (`onlyDir_msgsOf`), and appending the other direction's
half-close never perturbs it — so one peer closing its send side does not disturb
the peer still sending. This is exactly the interleaving RFC 9113 §5.1 permits on a
single stream and gRPC's HTTP/2 mapping requires.

## 2. Each direction honors per-stream HTTP/2 flow control (`grpc_bidi_flow`)

HTTP/2 flow control is *directional and per-stream* (RFC 9113 §5.2): each endpoint
maintains its own send window for the stream. We instantiate the proven
`H2.FlowWindow` ledger once per direction. Under *any* interleaving of DATA sends
and `WINDOW_UPDATE`s, each direction's total emitted DATA never exceeds its peer
initial stream window plus granted credits, and a direction whose window is zero
**parks** — it emits nothing and advances no counter — while the other direction,
a separate window, is untouched. Per-stream flow control genuinely bounds each
half independently.

## 3. The `grpc-status` trailer is the final frame, both directions (`grpc_bidi_trailers_final`)

Each direction terminates with a trailer frame carrying `grpc-status`. We prove
that after deframing all `n` data messages the remaining wire is **exactly** the
trailer frame and nothing follows it (it is the last frame), the trailer parses
back to the *exact* `GrpcStatus` code, and **no data frame is ever a trailer
frame** — so the terminal trailer is unambiguously the last frame, in both
directions.

## What is modelled vs. the host's

Everything is over pure byte lists / structured transcripts. The live HTTP/2
socket pump — reading request DATA off the client stream, response DATA off the
upstream, and the two trailing HEADERS blocks — is the host's byte I/O, exercised
through the same `dirWire` shape but with its syscalls outside this proof.
Residual, named: the h2 DATA/HEADERS read/write syscall loop is I/O, not modelled.
-/

namespace Proxy.GrpcBidiStream

open Reactor.Proxy.Grpc
open Proxy.GrpcProxy
open Proxy.GrpcWeb

/-! ## 1. The interleaved bidirectional transcript -/

/-- The two directions of a bidirectional stream. -/
inductive Dir where
  | client | server
deriving DecidableEq, Repr

/-- One event on the interleaved wire: either peer emits a message frame, or a
peer half-closes carrying its trailer block. The `List BidiEvent` is the global
order in which the two directions' frames actually appeared on the stream. -/
inductive BidiEvent where
  | msg (d : Dir) (f : Frame)
  | close (d : Dir) (trailer : List Nat)
deriving Repr

/-- The direction an event belongs to. -/
def dirOf : BidiEvent → Dir
  | .msg d _ => d
  | .close d _ => d

/-- Project an interleaved transcript onto one direction's ordered message list.
Order within the direction is preserved; the other direction and half-closes drop. -/
def msgsOf (d : Dir) : List BidiEvent → List Frame
  | [] => []
  | .msg d' f :: es => if d' = d then f :: msgsOf d es else msgsOf d es
  | .close _ _ :: es => msgsOf d es

/-- Keep only a direction's events (the demux the edge does per stream half). -/
def onlyDir (d : Dir) : List BidiEvent → List BidiEvent
  | [] => []
  | e :: es => if dirOf e = d then e :: onlyDir d es else onlyDir d es

/-- The wire bytes a single direction sends: its ordered messages as
length-prefixed frames, terminated by its trailer frame. -/
def dirWire (d : Dir) (t : List BidiEvent) (trailer : List Nat) : List Nat :=
  encodeStream (msgsOf d t) ++ encodeTrailerFrame trailer

/-- Projection is a monoid homomorphism on transcript concatenation. -/
theorem msgsOf_append (d : Dir) (a b : List BidiEvent) :
    msgsOf d (a ++ b) = msgsOf d a ++ msgsOf d b := by
  induction a with
  | nil => rfl
  | cons e es ih =>
    cases e with
    | msg d' f =>
      by_cases h : d' = d
      · simp only [List.cons_append, msgsOf, if_pos h, ih, List.cons_append]
      · simp only [List.cons_append, msgsOf, if_neg h, ih]
    | close d' blk =>
      simp only [List.cons_append, msgsOf, ih]

/-- **Half-close independence.** Discarding every event of the *other* direction
leaves a direction's message stream exactly as it was: the two directions do not
interfere. -/
theorem onlyDir_msgsOf (d : Dir) (t : List BidiEvent) :
    msgsOf d (onlyDir d t) = msgsOf d t := by
  induction t with
  | nil => rfl
  | cons e es ih =>
    cases e with
    | msg d' f =>
      by_cases h : d' = d <;> simp [onlyDir, dirOf, msgsOf, ih, h]
    | close d' blk =>
      by_cases h : d' = d <;> simp [onlyDir, dirOf, msgsOf, ih, h]

/-- **Bidi directions interleave in order, half-close is independent.** For any
interleaved transcript `t`:
* the client direction's wire deframes to *exactly* the client's messages in
  order, leaving its trailer frame as the untouched tail;
* the server direction's wire deframes to exactly the server's messages in order;
* (independence) dropping the other direction's events leaves each direction's
  message stream unchanged;
* (independent half-close) appending the *other* direction's half-close never
  perturbs a direction's message stream. -/
theorem grpc_bidi_interleave (t : List BidiEvent) (cTr sTr blk : List Nat)
    (hc : ∀ f ∈ msgsOf .client t, f.payload.length < 4294967296)
    (hs : ∀ f ∈ msgsOf .server t, f.payload.length < 4294967296) :
    decodeN (msgsOf .client t).length (dirWire .client t cTr)
        = some (msgsOf .client t, encodeTrailerFrame cTr)
    ∧ decodeN (msgsOf .server t).length (dirWire .server t sTr)
        = some (msgsOf .server t, encodeTrailerFrame sTr)
    ∧ msgsOf .client (onlyDir .client t) = msgsOf .client t
    ∧ msgsOf .server (onlyDir .server t) = msgsOf .server t
    ∧ msgsOf .client (t ++ [.close .server blk]) = msgsOf .client t
    ∧ msgsOf .server (t ++ [.close .client blk]) = msgsOf .server t := by
  refine ⟨?_, ?_, onlyDir_msgsOf .client t, onlyDir_msgsOf .server t, ?_, ?_⟩
  · simpa only [dirWire] using
      decodeN_encodeStream (msgsOf .client t) (encodeTrailerFrame cTr) hc
  · simpa only [dirWire] using
      decodeN_encodeStream (msgsOf .server t) (encodeTrailerFrame sTr) hs
  · rw [msgsOf_append]; simp [msgsOf]
  · rw [msgsOf_append]; simp [msgsOf]

/-! ## 2. Per-direction, per-stream HTTP/2 flow control -/

/-- **Each direction honors per-stream flow control.** A bidi stream carries two
independent send windows — one per direction. Given a well-formed flow state for
each direction and *any* interleaving of DATA sends and `WINDOW_UPDATE`s on each:
* each direction's total emitted DATA never exceeds its peer initial stream window
  plus its granted `WINDOW_UPDATE` credits (RFC 9113 §5.2);
* a direction whose stream window is zero **parks**: the send emits nothing and
  advances no counter — flow control genuinely blocks that half, independently. -/
theorem grpc_bidi_flow
    (cf sf : H2.FlowWindow.Flow) (ce se : List H2.FlowWindow.Event)
    (hc : cf.WF) (hs : sf.WF) :
    (cf.run ce).strSent ≤ (cf.run ce).strInit + (cf.run ce).strCredit
    ∧ (sf.run se).strSent ≤ (sf.run se).strInit + (sf.run se).strCredit
    ∧ (∀ (body : H2.Bytes) (maxFrame : Nat),
        sf.strWindow = 0 → 0 ≤ sf.connWindow → sf.send body maxFrame = sf) := by
  refine ⟨H2.FlowWindow.window_never_exceeded hc,
          H2.FlowWindow.window_never_exceeded hs, ?_⟩
  intro body maxFrame h0 hconn
  exact H2.FlowWindow.window_zero_stalls sf body maxFrame h0 hconn

/-! ## 3. The grpc-status trailer is the final frame, both directions -/

/-- **The `grpc-status` trailer is the last frame in each direction.** For a bidi
call where each direction sends its data messages then a single-digit `grpc-status`
trailer:
* deframing all `n` data messages leaves *exactly* the trailer frame as the tail —
  nothing follows it, so the trailer is the final frame (both directions);
* the terminal frame parses back to the *exact* `GrpcStatus` code (both directions);
* no data frame is a trailer frame, so the terminal trailer is unambiguous. -/
theorem grpc_bidi_trailers_final
    (cMsgs sMsgs : List Frame) (cs ss : GrpcStatus)
    (hc : ∀ f ∈ cMsgs, f.payload.length < 4294967296)
    (hs : ∀ f ∈ sMsgs, f.payload.length < 4294967296)
    (hcs : cs.code < 10) (hss : ss.code < 10) :
    decodeN cMsgs.length (encodeResponse cMsgs (statusTrailer cs))
        = some (cMsgs, encodeTrailerFrame (statusTrailer cs))
    ∧ decodeN sMsgs.length (encodeResponse sMsgs (statusTrailer ss))
        = some (sMsgs, encodeTrailerFrame (statusTrailer ss))
    ∧ splitResponse cMsgs.length (encodeResponse cMsgs (statusTrailer cs))
        = some (cMsgs, statusTrailer cs)
    ∧ splitResponse sMsgs.length (encodeResponse sMsgs (statusTrailer ss))
        = some (sMsgs, statusTrailer ss)
    ∧ statusOfTrailer (statusTrailer cs) = some cs
    ∧ statusOfTrailer (statusTrailer ss) = some ss
    ∧ (∀ f ∈ cMsgs, isTrailerFrame (flagByte f.compressed) = false)
    ∧ (∀ f ∈ sMsgs, isTrailerFrame (flagByte f.compressed) = false) := by
  have hcb : (statusTrailer cs).length < 4294967296 := by rw [statusTrailer_length]; omega
  have hsb : (statusTrailer ss).length < 4294967296 := by rw [statusTrailer_length]; omega
  refine ⟨?_, ?_, ?_, ?_, statusOfTrailer_statusTrailer cs hcs,
          statusOfTrailer_statusTrailer ss hss, ?_, ?_⟩
  · unfold encodeResponse
    exact decodeN_encodeStream cMsgs (encodeTrailerFrame (statusTrailer cs)) hc
  · unfold encodeResponse
    exact decodeN_encodeStream sMsgs (encodeTrailerFrame (statusTrailer ss)) hs
  · exact grpc_proxy_forwards cMsgs (statusTrailer cs) hc hcb
  · exact grpc_proxy_forwards sMsgs (statusTrailer ss) hs hsb
  · intro f _; exact data_not_trailer f
  · intro f _; exact data_not_trailer f

/-! ## Non-vacuity — real bidirectional streaming transcripts -/

/-- Concrete client-direction messages "ping","echo". -/
def cReq1 : Frame := { compressed := false, payload := [112, 105, 110, 103] }       -- "ping"
def cReq2 : Frame := { compressed := false, payload := [101, 99, 104, 111] }        -- "echo"

/-- Concrete server-direction messages "pong","done". -/
def sResp1 : Frame := { compressed := false, payload := [112, 111, 110, 103] }      -- "pong"
def sResp2 : Frame := { compressed := false, payload := [100, 111, 110, 101] }      -- "done"

/-- A genuinely interleaved transcript: client and server frames race on the wire
(C, S, C, then a client half-close, then a final server frame). -/
def demoTranscript : List BidiEvent :=
  [ .msg .client cReq1
  , .msg .server sResp1
  , .msg .client cReq2
  , .close .client []
  , .msg .server sResp2 ]

/-- **The projection recovers each direction's messages in order** — the client
sent `[ping, echo]`, the server `[pong, done]`, despite the wire interleaving. -/
example : msgsOf .client demoTranscript = [cReq1, cReq2] := by decide
example : msgsOf .server demoTranscript = [sResp1, sResp2] := by decide

/-- **Order is observable / non-vacuous:** the two directions' projections differ,
and the client projection ignores the interleaved server frames entirely. -/
example : msgsOf .client demoTranscript ≠ msgsOf .server demoTranscript := by decide

/-- **Independent half-close:** the client's `close` event (mid-transcript) does
not truncate the server stream — the server frame *after* it is still projected. -/
example : msgsOf .server demoTranscript = [sResp1, sResp2] := by decide

/-- The client-direction wire deframes back to exactly `[ping, echo]`, trailer as
the tail — a concrete instance of `grpc_bidi_interleave`. -/
example :
    decodeN 2 (dirWire .client demoTranscript (statusTrailer .ok))
      = some ([cReq1, cReq2], encodeTrailerFrame (statusTrailer .ok)) := by decide

/-! ### Flow control fires on a real trajectory -/

/-- The server-direction send-side flow: stream initial window 10, plenty of
connection window. -/
def demoServerFlow : H2.FlowWindow.Flow := H2.FlowWindow.Flow.fresh 1000000 10

/-- A real send-then-credit-then-send trajectory on the server direction. -/
def demoServerTrace : List H2.FlowWindow.Event :=
  [ H2.FlowWindow.Event.send [1, 2, 3, 4] 16384
  , H2.FlowWindow.Event.strUpdate 20
  , H2.FlowWindow.Event.send [5, 6, 7, 8, 9, 10, 11, 12] 16384 ]

/-- The server-direction flow is well-formed to start. -/
theorem demoServerFlow_WF : demoServerFlow.WF := by
  refine H2.FlowWindow.Flow.fresh_WF ?_ ?_ ?_ ?_ <;> decide

/-- **Non-vacuous flow bound:** on the demo trajectory the server direction really
emits 12 octets (> 0), within `10 + 20 = 30` granted. -/
theorem demoServer_sent : (demoServerFlow.run demoServerTrace).strSent = 12 := by decide

theorem demoServer_bound :
    (demoServerFlow.run demoServerTrace).strSent ≤
      (demoServerFlow.run demoServerTrace).strInit
        + (demoServerFlow.run demoServerTrace).strCredit :=
  H2.FlowWindow.window_never_exceeded demoServerFlow_WF

/-- **A zero-window direction really stalls:** a server direction whose stream
window is zero emits nothing regardless of the payload offered. -/
def stalledServerFlow : H2.FlowWindow.Flow := H2.FlowWindow.Flow.fresh 1000000 0

example (maxFrame : Nat) : stalledServerFlow.send [1, 2, 3] maxFrame = stalledServerFlow :=
  H2.FlowWindow.window_zero_stalls stalledServerFlow [1, 2, 3] maxFrame rfl (by decide)

/-! ### Trailers-final fires on real per-direction responses -/

/-- **The trailer is the last frame:** the server response `[pong, done]` +
`grpc-status: 0` deframes to the two messages then exactly the trailer frame, and
the trailer reads back as `Ok`. -/
example :
    decodeN 2 (encodeResponse [sResp1, sResp2] (statusTrailer .ok))
        = some ([sResp1, sResp2], encodeTrailerFrame (statusTrailer .ok))
    ∧ statusOfTrailer (statusTrailer .ok) = some GrpcStatus.ok := by decide

/-- **Status matters (non-vacuous):** a different `grpc-status` (NotFound, 5) reads
back to a different code — trailer recovery is not the constant function. -/
example :
    statusOfTrailer (statusTrailer .ok) ≠ statusOfTrailer (statusTrailer .notFound) := by decide

/-- **Framing is load-bearing:** dropping one byte off the server stream breaks the
deframe of that message count — the length prefix carries the boundary. -/
example :
    decodeN 1 (encodeStream [sResp1])
      ≠ decodeN 1 ((encodeStream [sResp1]).dropLast) := by decide

end Proxy.GrpcBidiStream
