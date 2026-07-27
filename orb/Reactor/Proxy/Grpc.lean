import Proxy.Basic

/-!
# Reactor.Proxy.Grpc — gRPC message framing, status trailers, and gRPC-Web translation

gRPC runs over HTTP/2: the h2 engine owns the stream and DATA frames; gRPC adds a
message framing *inside* the DATA payload and a `grpc-status` trailer. This module
is the proven core of the gRPC/gRPC-Web proxy: the wire codec the edge must decode
faithfully to find message boundaries, enforce size limits, and translate to
gRPC-Web for browsers. The byte transport (streaming the h2 DATA frames through)
is the host's, reusing the streaming passthrough; the *framing decisions* are here.

## gRPC message framing (Length-Prefixed-Message)

Each message on the wire is a 5-byte header followed by the payload:

```
  +--------+--------+--------+--------+--------+============+
  | flag   |          length (u32, big-endian) | payload…   |
  +--------+--------+--------+--------+--------+============+
     1 byte              4 bytes                length bytes
```

`flag` bit 0 is the compressed flag (0 = identity, 1 = compressed). `length` is
the payload byte count. `encodeFrame`/`decodeFrame` are inverse
(`decodeFrame_encodeFrame`): decoding an encoded frame recovers the flag, the
exact payload, and the untouched tail — so the edge splits a stream into messages
without loss. The numeric length codec is faithful for every 32-bit length
(`rd32_be32`).

## grpc-status

The RPC result is a trailer `grpc-status: <n>` (`0` = OK). `GrpcStatus` enumerates
the 17 canonical codes (`Ok = 0 … Unauthenticated = 16`); `httpToGrpc` maps an
HTTP status the origin might return onto the gRPC code the edge surfaces
(`404 → Unimplemented`, `429/503 → Unavailable`, …).

## gRPC-Web translation

gRPC-Web carries the SAME length-prefixed data frames as gRPC — the message
framing is byte-identical (`grpcweb_data_identical`) — but delivers the trailers
*in the body* as a final frame whose flag byte has bit 7 set (`0x80`), instead of
an HTTP/2 trailing HEADERS frame. `encodeTrailerFrame` builds that frame from a
`name: value\r\n` block; `isTrailerFrame` (flag ≥ `0x80`) distinguishes it from a
data frame (whose flag ≤ 1), so the translation is unambiguous
(`data_not_trailer`, `trailer_is_trailer`). Translating gRPC → gRPC-Web appends
the trailer frame after the data frames; gRPC-Web → gRPC strips it. The message
frames pass through unchanged, so passthrough is proven-faithful by the shared
codec.

## Deferred

* **gRPC-Web text mode** (`application/grpc-web-text`): base64 of the whole body.
  The framing translation above is mode-independent; the base64 transcode is a
  standard encoding layer, named as residual (see the report).
-/

namespace Reactor.Proxy.Grpc

/-! ## Big-endian u32 length codec -/

/-- Encode a length as 4 big-endian bytes. -/
def be32 (n : Nat) : List Nat :=
  [n / 16777216 % 256, n / 65536 % 256, n / 256 % 256, n % 256]

/-- Decode 4 big-endian bytes back to a length. -/
def rd32 : List Nat → Nat
  | [b0, b1, b2, b3] => b0 * 16777216 + b1 * 65536 + b2 * 256 + b3
  | _ => 0

/-- **The length codec is faithful** for every 32-bit length. -/
theorem rd32_be32 {n : Nat} (h : n < 4294967296) : rd32 (be32 n) = n := by
  simp only [be32, rd32]; omega

/-! ## The message frame -/

/-- One gRPC length-prefixed message: the compressed flag and the payload bytes
(each a byte value `< 256`). -/
structure Frame where
  compressed : Bool
  payload : List Nat
deriving DecidableEq, Repr

/-- The header flag byte for a compressed disposition. -/
def flagByte (compressed : Bool) : Nat := if compressed then 1 else 0

/-- Encode a frame: `flag :: be32 length ++ payload`. -/
def encodeFrame (f : Frame) : List Nat :=
  flagByte f.compressed :: be32 f.payload.length ++ f.payload

/-- Decode the leading frame of a byte stream, returning the frame and the
untouched tail; `none` if the header or payload is incomplete. -/
def decodeFrame : List Nat → Option (Frame × List Nat)
  | flag :: b0 :: b1 :: b2 :: b3 :: body =>
    let len := rd32 [b0, b1, b2, b3]
    if len ≤ body.length then
      some ({ compressed := flag == 1, payload := body.take len }, body.drop len)
    else none
  | _ => none

/-- **Faithful decode.** Decoding an encoded frame (followed by any tail)
recovers the frame exactly and returns the tail untouched — the edge splits a
message stream without loss or corruption. -/
theorem decodeFrame_encodeFrame (f : Frame) (rest : List Nat)
    (hlen : f.payload.length < 4294967296) :
    decodeFrame (encodeFrame f ++ rest) = some (f, rest) := by
  have hrd : rd32 (be32 f.payload.length) = f.payload.length := rd32_be32 hlen
  simp only [encodeFrame, be32, List.cons_append, List.append_assoc,
    List.nil_append, decodeFrame] at hrd ⊢
  rw [hrd, if_pos (by simp)]
  have hflag : (flagByte f.compressed == 1) = f.compressed := by
    cases f.compressed <;> simp [flagByte]
  rw [List.take_left, List.drop_left, hflag]

/-- The decoded flag reflects the compressed bit; the decoded payload is exactly
the input payload (a direct corollary, stated for readability). -/
theorem decode_roundtrip_fields (f : Frame) (hlen : f.payload.length < 4294967296) :
    ∃ p, decodeFrame (encodeFrame f) = some (f, p) ∧ p = [] := by
  refine ⟨[], ?_, rfl⟩
  have := decodeFrame_encodeFrame f [] hlen
  simpa using this

/-! ### Non-vacuity: real gRPC frames -/

/-- A real, uncompressed 5-byte-payload frame: flag `0x00`, length `0x00000005`,
payload "hello" (`0x68 0x65 0x6c 0x6c 0x6f`). Decodes to exactly that message. -/
example :
    decodeFrame [0, 0, 0, 0, 5, 104, 101, 108, 108, 111]
      = some ({ compressed := false, payload := [104, 101, 108, 108, 111] }, []) := by
  decide

/-- Two frames back to back: the decoder returns the first and leaves the second
as the tail. -/
example :
    decodeFrame [0, 0, 0, 0, 2, 1, 2, 0, 0, 0, 0, 1, 9]
      = some ({ compressed := false, payload := [1, 2] }, [0, 0, 0, 0, 1, 9]) := by
  decide

/-- A truncated header (fewer than 5 bytes) does not decode. -/
example : decodeFrame [0, 0, 0] = none := by decide

/-- A declared length exceeding the available body does not decode. -/
example : decodeFrame [0, 0, 0, 0, 9, 1, 2] = none := by decide

/-! ## grpc-status codes -/

/-- The canonical gRPC status codes (RFC/grpc `code.proto`). -/
inductive GrpcStatus where
  | ok | cancelled | unknown | invalidArgument | deadlineExceeded | notFound
  | alreadyExists | permissionDenied | resourceExhausted | failedPrecondition
  | aborted | outOfRange | unimplemented | internal | unavailable | dataLoss
  | unauthenticated
deriving DecidableEq, Repr

/-- The numeric code for a status (`0 … 16`). -/
def GrpcStatus.code : GrpcStatus → Nat
  | ok => 0 | cancelled => 1 | unknown => 2 | invalidArgument => 3
  | deadlineExceeded => 4 | notFound => 5 | alreadyExists => 6
  | permissionDenied => 7 | resourceExhausted => 8 | failedPrecondition => 9
  | aborted => 10 | outOfRange => 11 | unimplemented => 12 | internal => 13
  | unavailable => 14 | dataLoss => 15 | unauthenticated => 16

/-- Only `Ok` (`grpc-status: 0`) is success. -/
def GrpcStatus.isOk : GrpcStatus → Bool
  | ok => true | _ => false

theorem ok_code_zero : GrpcStatus.ok.code = 0 := rfl
theorem isOk_iff_code_zero (s : GrpcStatus) : s.isOk = true ↔ s.code = 0 := by
  cases s <;> simp [GrpcStatus.isOk, GrpcStatus.code]

/-- Map an origin HTTP status onto the gRPC status the edge surfaces. -/
def httpToGrpc (status : Nat) : GrpcStatus :=
  if status == 200 then .ok
  else if status == 400 then .invalidArgument
  else if status == 401 then .unauthenticated
  else if status == 403 then .permissionDenied
  else if status == 404 then .unimplemented
  else if status == 408 then .deadlineExceeded
  else if status == 429 then .unavailable
  else if status == 500 then .internal
  else if status == 501 then .unimplemented
  else if status == 503 then .unavailable
  else if status == 504 then .deadlineExceeded
  else .unknown

example : httpToGrpc 200 = .ok := rfl
example : httpToGrpc 404 = .unimplemented := rfl
example : httpToGrpc 503 = .unavailable := rfl
example : httpToGrpc 418 = .unknown := rfl

/-! ## gRPC-Web framing translation -/

/-- The gRPC-Web trailer-frame flag: bit 7 set (`0x80`). -/
def trailerFlag : Nat := 128

/-- A frame's flag marks a trailer frame iff bit 7 is set. Data frames use flag
`0`/`1`, so `≥ 128` cleanly separates the two. -/
def isTrailerFrame (flag : Nat) : Bool := decide (trailerFlag ≤ flag)

/-- **A data frame is never mistaken for a trailer frame.** -/
theorem data_not_trailer (f : Frame) : isTrailerFrame (flagByte f.compressed) = false := by
  cases f.compressed <;> simp [isTrailerFrame, flagByte, trailerFlag]

/-- **The trailer frame is a trailer frame.** -/
theorem trailer_is_trailer : isTrailerFrame trailerFlag = true := by
  simp [isTrailerFrame, trailerFlag]

/-- Encode a trailer block (already `name: value\r\n`-joined bytes) as a
gRPC-Web trailer frame: `0x80 :: be32 len ++ block`. -/
def encodeTrailerFrame (block : List Nat) : List Nat :=
  trailerFlag :: be32 block.length ++ block

/-- Empty trailers encode to exactly `[0x80, 0, 0, 0, 0]`. -/
example : encodeTrailerFrame [] = [128, 0, 0, 0, 0] := by decide

/-- The data-frame codec is byte-identical between gRPC and gRPC-Web, so message
frames pass through translation unchanged. `encodeFrameWeb` is definitionally the
gRPC encoder — the passthrough is faithful by construction. -/
def encodeFrameWeb (f : Frame) : List Nat := encodeFrame f

theorem grpcweb_data_identical (f : Frame) : encodeFrameWeb f = encodeFrame f := rfl

/-- **gRPC → gRPC-Web is faithful on messages.** A data frame emitted into a
gRPC-Web response decodes back to the same message (the framing is shared). -/
theorem grpcweb_message_roundtrip (f : Frame) (rest : List Nat)
    (hlen : f.payload.length < 4294967296) :
    decodeFrame (encodeFrameWeb f ++ rest) = some (f, rest) :=
  decodeFrame_encodeFrame f rest hlen

/-- **A gRPC-Web response = data frames then a trailer frame.** The trailer frame
is distinguishable (`isTrailerFrame` on its flag), so gRPC-Web → gRPC recovers the
data by taking frames until the trailer frame. -/
def buildGrpcWebResponse (dataFrames : List Nat) (trailerBlock : List Nat) : List Nat :=
  dataFrames ++ encodeTrailerFrame trailerBlock

/-- The trailer frame that terminates a gRPC-Web response is always recognizable:
its flag byte is `0x80`. -/
theorem grpcweb_trailer_marked (block : List Nat) :
    (encodeTrailerFrame block).headD 0 = trailerFlag := by
  simp [encodeTrailerFrame, trailerFlag]

/-! ## grpc.health.v1 serving status -/

/-- The `grpc.health.v1.HealthCheckResponse.ServingStatus` enum. -/
inductive ServingStatus where
  | unknown | serving | notServing | serviceUnknown
deriving DecidableEq, Repr

def ServingStatus.code : ServingStatus → Nat
  | unknown => 0 | serving => 1 | notServing => 2 | serviceUnknown => 3

/-- Only `Serving` (`1`) counts as healthy for the health-check pick filter. -/
def ServingStatus.isHealthy : ServingStatus → Bool
  | serving => true | _ => false

def ServingStatus.ofCode : Nat → ServingStatus
  | 1 => .serving | 2 => .notServing | 3 => .serviceUnknown | _ => .unknown

theorem serving_healthy : ServingStatus.serving.isHealthy = true := rfl
theorem notServing_unhealthy : ServingStatus.notServing.isHealthy = false := rfl
theorem ofCode_code (s : ServingStatus) : ServingStatus.ofCode s.code = s := by
  cases s <;> rfl

/-! ## The byte-level host seam -/

/-- **gRPC frame length, byte seam.** Input is at least the 5-byte header; output
is the decimal-ASCII payload length (so the host can find the message boundary
and enforce the max-message-size limit while streaming the h2 DATA through the
proven passthrough). EMPTY if fewer than 5 header bytes are present. -/
@[export drorb_grpc_frame_len]
def grpcFrameLen (input : ByteArray) : ByteArray :=
  match input.toList with
  | _flag :: b0 :: b1 :: b2 :: b3 :: _ =>
    (toString (rd32 [b0.toNat, b1.toNat, b2.toNat, b3.toNat])).toUTF8
  | _ => ByteArray.empty

end Reactor.Proxy.Grpc
