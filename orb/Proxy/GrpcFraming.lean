import Proxy.GrpcProxy

/-!
# Proxy.GrpcFraming — gRPC message-framing *depth*: layout, streaming buffer, trailer seam

`Reactor.Proxy.Grpc` proves the single-frame length-prefixed codec and
`Proxy.GrpcProxy` lifts it to an ordered message stream and a verbatim relay.
This module proves the three *framing-depth* properties a faithful edge must hold
when it decodes a gRPC stream one incremental read at a time and must decide,
per read, whether it holds a whole message, a fragment to buffer, or the RPC
status — and where the status actually lives on the wire.

## 1. Length-prefixed layout is exact (`grpc_length_prefixed_frame`)

A gRPC message on the wire is `1-byte compressed-flag :: 4-byte big-endian length
:: payload`. The header is exactly five bytes, the length field is exactly four
big-endian bytes that decode back to the payload byte count, and the whole frame
followed by any tail deframes to *exactly* the original frame with the tail
returned untouched. Framing and deframing are inverse with no slack.

## 2. A partial frame buffers — it never mis-parses (`grpc_frame_partial`)

The edge reads bytes incrementally. Two incompleteness cases must both yield
"need more bytes", never a wrong parse:

* **Short header** — any buffer under five bytes cannot be decoded at all
  (`∀ pre, pre.length < 5 → decodeFrame pre = none`), so a header split across
  reads is buffered, not misread.
* **Partial payload** — a *complete* five-byte header whose declared length
  exceeds the bytes actually buffered (`k < payload.length` bytes present) yields
  `none`: the decoder refuses to hand up a truncated message.

And buffering is lossless: once the remaining bytes arrive, the *same* frame
decodes cleanly (`decodeFrame (encodeFrame f) = some (f, [])`). This is the
progress half — a buffering parser that could never complete would be useless.

## 3. `grpc-status` rides the HTTP/2 trailer, not the DATA body (`grpc_status_in_trailer`)

Native gRPC-over-HTTP/2 puts the message payloads in DATA frames (the body) and
the RPC result in a *trailing HEADERS* block: `grpc-status: <code>` /
`grpc-message: <text>`. This is the structural distinction from gRPC-Web (which
carries the trailer *in* the body as an `0x80`-flagged frame). We model an
HTTP/2 gRPC response as `(headers, body, trailers)` and prove:

* the `grpc-status` header is found in the **trailers** block and reads back to
  the exact `GrpcStatus`;
* the initial **headers** block carries no `grpc-status` (it holds `:status` /
  `content-type`);
* every frame in the **body** is a *data* frame (`isTrailerFrame` false) — there
  is no in-band trailer frame in native h2, unlike gRPC-Web;
* the body deframes to exactly the data messages, in order, with nothing left
  over — the status is not smuggled into the message stream.

## What is modelled vs. the host's

Everything here is over pure byte lists / structured header maps. Reading the h2
DATA/HEADERS frames off the socket and re-emitting them is the host's byte pump.
Residual, named: the h2 frame-layer read/write syscall loop is I/O, not modelled.
-/

namespace Proxy.GrpcFraming

open Reactor.Proxy.Grpc
open Proxy.GrpcProxy

/-! ## 1. Length-prefixed layout is exact -/

/-- **A gRPC message = 1-byte flag + 4-byte BE length + payload; frames/deframes
exactly.** The length prefix is exactly four big-endian bytes decoding to the
payload length, the whole frame is a five-byte header plus the payload, and
`decodeFrame` recovers the frame and leaves any tail untouched. -/
theorem grpc_length_prefixed_frame (f : Frame) (rest : List Nat)
    (hlen : f.payload.length < 4294967296) :
    decodeFrame (encodeFrame f ++ rest) = some (f, rest)
    ∧ (be32 f.payload.length).length = 4
    ∧ rd32 (be32 f.payload.length) = f.payload.length
    ∧ (encodeFrame f).length = 5 + f.payload.length := by
  refine ⟨decodeFrame_encodeFrame f rest hlen, rfl, rd32_be32 hlen, ?_⟩
  simp only [encodeFrame, be32, List.cons_append, List.nil_append,
    List.length_cons, List.length_append, List.length_nil]
  omega

/-! ## 2. A partial frame buffers — it never mis-parses -/

/-- **A partial frame buffers, does not mis-parse.** (a) Any buffer shorter than
the five-byte header cannot decode. (b) A full header whose declared length
exceeds the `k < payload.length` bytes buffered decodes to `none` — no truncated
message is handed up. (c) Once the frame is complete it decodes cleanly, so the
buffering is lossless (progress). -/
theorem grpc_frame_partial (f : Frame) (k : Nat)
    (hlen : f.payload.length < 4294967296)
    (hpartial : k < f.payload.length) :
    (∀ pre : List Nat, pre.length < 5 → decodeFrame pre = none)
    ∧ decodeFrame (flagByte f.compressed :: be32 f.payload.length ++ f.payload.take k) = none
    ∧ decodeFrame (encodeFrame f) = some (f, []) := by
  refine ⟨?_, ?_, ?_⟩
  · -- (a) short header buffers, never mis-parses
    intro pre h
    rcases pre with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, tl⟩⟩⟩⟩⟩
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · simp only [List.length_cons] at h; omega
  · -- (b) full header, partial payload buffers
    obtain ⟨a, b, c, d, he⟩ : ∃ a b c d, be32 f.payload.length = [a, b, c, d] :=
      ⟨_, _, _, _, rfl⟩
    have hrd : rd32 [a, b, c, d] = f.payload.length := by rw [← he]; exact rd32_be32 hlen
    have hbody : (f.payload.take k).length = k := by rw [List.length_take]; omega
    rw [he]
    simp only [List.cons_append, List.nil_append, decodeFrame]
    rw [hrd, hbody, if_neg (by omega)]
  · -- (c) completes losslessly
    simpa using decodeFrame_encodeFrame f [] hlen

/-! ## 3. `grpc-status` rides the HTTP/2 trailer, not the body -/

/-- ASCII header name `"grpc-status"`. -/
def grpcStatusKey : List Nat := [103, 114, 112, 99, 45, 115, 116, 97, 116, 117, 115]

/-- ASCII header name `"grpc-message"`. -/
def grpcMessageKey : List Nat := [103, 114, 112, 99, 45, 109, 101, 115, 115, 97, 103, 101]

/-- ASCII pseudo-header name `":status"` (the HTTP/2 response status). -/
def statusPseudoKey : List Nat := [58, 115, 116, 97, 116, 117, 115]

/-- ASCII header name `"content-type"`. -/
def contentTypeKey : List Nat := [99, 111, 110, 116, 101, 110, 116, 45, 116, 121, 112, 101]

/-- Encode a `Nat` (`< 100`) as its ASCII decimal digits — the `grpc-status`
value is decimal text (`"0" … "16"`). -/
def asciiOfNat (n : Nat) : List Nat :=
  if n < 10 then [n + 48] else [n / 10 + 48, n % 10 + 48]

/-- Parse one or two ASCII decimal digits back to a `Nat`. -/
def natOfAscii : List Nat → Option Nat
  | [d] => if 48 ≤ d ∧ d ≤ 57 then some (d - 48) else none
  | [d0, d1] =>
      if (48 ≤ d0 ∧ d0 ≤ 57) ∧ (48 ≤ d1 ∧ d1 ≤ 57)
      then some ((d0 - 48) * 10 + (d1 - 48)) else none
  | _ => none

/-- The `grpc-status` trailer value for a status: its numeric code as ASCII decimal. -/
def statusDigits (s : GrpcStatus) : List Nat := asciiOfNat s.code

/-- Recover a `GrpcStatus` from a decimal `grpc-status` value. -/
def statusOfDigits (l : List Nat) : Option GrpcStatus := (natOfAscii l).bind grpcOfCode

/-- The `grpc-status` decimal value round-trips to the exact status, for every
canonical code (`0 … 16`). Non-vacuous inverse: the code survives, not raw bytes. -/
theorem statusOfDigits_statusDigits (s : GrpcStatus) :
    statusOfDigits (statusDigits s) = some s := by
  cases s <;> decide

/-- Ordered association lookup in a header block. -/
def lookupTrailer (key : List Nat) : List (List Nat × List Nat) → Option (List Nat)
  | [] => none
  | (k, v) :: rest => if k = key then some v else lookupTrailer key rest

/-- An HTTP/2 gRPC response: the ordered data messages (carried in DATA frames =
the body), the RPC `status`, and the human-readable `message` (both carried in
the trailing HEADERS block). -/
structure GrpcH2Response where
  bodyMessages : List Frame
  status : GrpcStatus
  message : List Nat

/-- The initial HEADERS block: `:status: 200`, `content-type: application/grpc`.
No `grpc-status` here — that is the *trailing* HEADERS. -/
def h2Headers (r : GrpcH2Response) : List (List Nat × List Nat) :=
  [(statusPseudoKey, [50, 48, 48]),
   (contentTypeKey, [97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 47, 103, 114, 112, 99])]

/-- The trailing HEADERS block: `grpc-status: <code>`, `grpc-message: <text>`. -/
def h2Trailers (r : GrpcH2Response) : List (List Nat × List Nat) :=
  [(grpcStatusKey, statusDigits r.status),
   (grpcMessageKey, r.message)]

/-- The DATA body: the ordered length-prefixed data messages, nothing else. -/
def h2Body (r : GrpcH2Response) : List Nat := encodeStream r.bodyMessages

/-- **`grpc-status` / `grpc-message` ride the HTTP trailer, not the body.** For a
native gRPC-over-HTTP/2 response:
* the `grpc-status` header is found in the **trailers** block and reads back to
  the exact `GrpcStatus`;
* the initial **headers** block contains no `grpc-status`;
* every frame in the **body** is a data frame (never an in-band trailer frame —
  the distinction from gRPC-Web);
* the body deframes to exactly the data messages in order, tail empty — the
  status is not carried in the message stream. -/
theorem grpc_status_in_trailer (r : GrpcH2Response)
    (hm : ∀ f ∈ r.bodyMessages, f.payload.length < 4294967296) :
    lookupTrailer grpcStatusKey (h2Trailers r) = some (statusDigits r.status)
    ∧ statusOfDigits (statusDigits r.status) = some r.status
    ∧ lookupTrailer grpcStatusKey (h2Headers r) = none
    ∧ (∀ f ∈ r.bodyMessages, isTrailerFrame (flagByte f.compressed) = false)
    ∧ decodeN r.bodyMessages.length (h2Body r) = some (r.bodyMessages, []) := by
  refine ⟨?_, statusOfDigits_statusDigits r.status, ?_, ?_, ?_⟩
  · simp [h2Trailers, lookupTrailer]
  · simp only [h2Headers]; decide
  · intro f _; exact data_not_trailer f
  · simpa [h2Body] using decodeN_encodeStream r.bodyMessages [] hm

/-! ### Non-vacuity: real gRPC streaming and a real h2 response -/

/-- A concrete "hello" frame (flag 0, length 5, payload `h e l l o`) plus a tail:
deframes to exactly the message and returns the tail untouched. -/
example :
    decodeFrame ([0, 0, 0, 0, 5, 104, 101, 108, 108, 111] ++ [0, 0, 0, 0, 1, 9])
      = some ({ compressed := false, payload := [104, 101, 108, 108, 111] },
              [0, 0, 0, 0, 1, 9]) := by decide

/-- **Partial payload buffers:** a header declaring length 9 with only 2 payload
bytes present yields `none` — not a truncated 2-byte message. -/
example : decodeFrame [0, 0, 0, 0, 9, 1, 2] = none := by decide

/-- **Short header buffers:** three bytes of a header cannot decode. -/
example : decodeFrame [0, 0, 0] = none := by decide

/-- **Progress:** once the missing 7 bytes arrive the full frame decodes cleanly. -/
example :
    decodeFrame [0, 0, 0, 0, 9, 1, 2, 3, 4, 5, 6, 7, 8, 9]
      = some ({ compressed := false, payload := [1, 2, 3, 4, 5, 6, 7, 8, 9] }, []) := by
  decide

/-- A real `NotFound` (code 5) status: its trailer value is ASCII `"5"` (`[53]`)
and parses back to exactly `NotFound`. -/
example :
    (statusDigits GrpcStatus.notFound = [53]
     ∧ statusOfDigits [53] = some GrpcStatus.notFound) := by decide

/-- A real two-digit status `Unauthenticated` (code 16): value `"16"` (`[49, 54]`),
round-trips exactly — the decimal codec handles multi-digit codes. -/
example :
    (statusDigits GrpcStatus.unauthenticated = [49, 54]
     ∧ statusOfDigits [49, 54] = some GrpcStatus.unauthenticated) := by decide

/-- **Status lives in the trailer, not the header block.** For a concrete
response, `grpc-status` is absent from the initial headers and present (as `"14"`,
`Unavailable`) in the trailers. -/
example :
    let r : GrpcH2Response :=
      { bodyMessages := [{ compressed := false, payload := [1, 2, 3] }],
        status := GrpcStatus.unavailable, message := [] }
    lookupTrailer grpcStatusKey (h2Headers r) = none
    ∧ lookupTrailer grpcStatusKey (h2Trailers r) = some [49, 52] := by decide

/-- **Mutant (status matters):** different statuses give different trailer values —
`grpc-status` recovery is not the constant function. -/
example : statusDigits GrpcStatus.ok ≠ statusDigits GrpcStatus.unavailable := by decide

/-- **Mutant (the body has no trailer frame):** a native-h2 data frame is never an
in-band trailer frame — this is what separates it from gRPC-Web. -/
example :
    isTrailerFrame (flagByte false) = false
    ∧ isTrailerFrame trailerFlag = true := by decide

end Proxy.GrpcFraming
