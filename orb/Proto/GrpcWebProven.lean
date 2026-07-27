/-
# Proto.GrpcWebProven — the DEPLOYED gRPC-Web serve is faithful (rp.3 / rp.2 / px.15)

PROVE-WHAT-RUNS for `Reactor.GrpcWebServe.drorbServeGrpcWeb` (`@[export drorb_serve_grpcweb]`),
the edge-terminated gRPC-Web unary responder. Driven against the compiled export by
`Reactor.GrpcWebDrive`.

Theorems:
  * `grpcWebBody_echo` — the response body decodes back to the echoed message frame,
    with the trailer frame as the untouched tail (the gRPC length-prefixed framing is
    reconstructed byte-for-byte; rp.2).
  * `grpcWebBody_trailer_marked` — the tail-frame flag is `0x80`, so gRPC-Web → gRPC can
    find the trailer boundary (rp.3).
  * `grpcWebResponse_body_suffix` — the gRPC-Web frame bytes are a suffix of the served
    HTTP response (nothing after them; the deployed serializer's Content-Length is fixed).
  * `drorbServeGrpcWeb_toList` — on a gRPC-Web request the served bytes ARE
    `serialize (grpcWebResponse …)` (ties the export to the proven response).
  * `served_grpcweb_echo` — end-to-end: on a gRPC-Web request the served bytes carry the
    echo-frame + trailer as a suffix.
-/
import Reactor.GrpcWebServe
import Proto.Kernel.Shortcuts

namespace Proto.GrpcWebProven

open Reactor.Proxy.Grpc
open Reactor.GrpcWebServe
open Proto.Kernel

/-! ## The framing is faithful -/

/-- **`grpcWebBody_echo`.** The response body decodes to the echoed data frame, leaving the
trailer frame as the tail — the gRPC length-prefixed framing is reconstructed exactly. -/
theorem grpcWebBody_echo (p : List Nat) (h : p.length < 4294967296) :
    decodeFrame (grpcWebBody p)
      = some ({ compressed := false, payload := p }, encodeTrailerFrame okTrailerBlock) := by
  unfold grpcWebBody buildGrpcWebResponse
  exact decodeFrame_encodeFrame { compressed := false, payload := p }
    (encodeTrailerFrame okTrailerBlock) h

/-- **`grpcWebBody_trailer_marked`.** The frame following the data frame is a trailer
frame (flag `0x80`) — gRPC-Web → gRPC unambiguously finds the trailer boundary. -/
theorem grpcWebBody_trailer_marked :
    isTrailerFrame ((encodeTrailerFrame okTrailerBlock).headD 0) = true := by
  rw [grpcweb_trailer_marked]; exact trailer_is_trailer

/-! ## The HTTP wrapping is faithful -/

/-- **`grpcWebResponse_body_suffix`.** The gRPC-Web frame bytes are a suffix of the served
HTTP response: nothing is emitted after the framed body. -/
theorem grpcWebResponse_body_suffix (p : List Nat) :
    natsToBytes (grpcWebBody p) <:+ _root_.Reactor.serialize (grpcWebResponse p) :=
  _root_.Reactor.serialize_body_suffix (grpcWebResponse p)

/-- **`drorbServeGrpcWeb_toList`.** On a gRPC-Web request the served bytes ARE the
serialized proven `grpcWebResponse`. -/
theorem drorbServeGrpcWeb_toList (input : ByteArray)
    (hgw : isGrpcWebReq input.toList = true) :
    (drorbServeGrpcWeb input).toList
      = _root_.Reactor.serialize (grpcWebResponse (echoPayload input.toList)) := by
  unfold drorbServeGrpcWeb
  rw [Shortcuts.ba_toList_eq, if_pos hgw]

/-- **`served_grpcweb_echo`.** End-to-end: on a gRPC-Web request, the served response
bytes carry the echo data frame + trailer frame as a suffix. -/
theorem served_grpcweb_echo (input : ByteArray)
    (hgw : isGrpcWebReq input.toList = true) :
    natsToBytes (grpcWebBody (echoPayload input.toList)) <:+ (drorbServeGrpcWeb input).toList := by
  rw [drorbServeGrpcWeb_toList input hgw]
  exact grpcWebResponse_body_suffix _

/-! ## Non-vacuity: a real gRPC-Web request round-trips -/

/-- A real gRPC-Web unary request: `POST` a length-prefixed `"hi"` message. -/
def exReqHead : String :=
  "POST /echo.Echo/Say HTTP/1.1\r\nContent-Type: application/grpc-web+proto\r\n\r\n"
/-- The request frame: uncompressed `"hi"` (`0x68 0x69`). -/
def exFrame : List Nat := encodeFrame { compressed := false, payload := [104, 105] }
/-- The full request bytes. -/
def exReq : ByteArray := ByteArray.mk (exReqHead.toUTF8.toList ++ natsToBytes exFrame).toArray

-- The request is recognized as gRPC-Web and its message payload is decoded ("hi").
#guard isGrpcWebReq exReq.toList = true
#guard echoPayload exReq.toList = [104, 105]
-- The served response body decodes to the echoed "hi" frame, trailer frame as tail.
#guard (decodeFrame (grpcWebBody (echoPayload exReq.toList)))
        = some ({ compressed := false, payload := [104, 105] }, encodeTrailerFrame okTrailerBlock)
-- The trailer block spells `grpc-status:0\r\n`.
#guard okTrailerBlock = [103,114,112,99,45,115,116,97,116,117,115,58,48,13,10]

#print axioms grpcWebBody_echo
#print axioms grpcWebBody_trailer_marked
#print axioms grpcWebResponse_body_suffix
#print axioms drorbServeGrpcWeb_toList
#print axioms served_grpcweb_echo

end Proto.GrpcWebProven
