/-
# Reactor.GrpcWebServe — a DEPLOYED gRPC-Web unary edge endpoint (rp.3 / rp.2 / px.15)

The proven gRPC/gRPC-Web wire codec (`Reactor.Proxy.Grpc`) was a MISSING-row leaf
(`[proven leaf, inert: grpc_bidi / grpc_length_prefixed_frame]`): the framing was
proven but no served endpoint reached it. This module WIRES it: an edge-terminated
gRPC-Web unary responder that speaks HTTP/1.1 (curl-drivable, no h2 needed), reusing
the deployed HTTP response serializer (`Reactor.serialize`) so the framing/Content-Length
discipline is the same the orb uses on every response.

Behaviour: on a request carrying `content-type: application/grpc-web...`, the edge decodes
the request's length-prefixed message frame (`decodeFrame`) and answers `200` with a
gRPC-Web body = one data frame echoing the request payload, followed by the trailer frame
(flag `0x80`) carrying `grpc-status:0` (OK). A non-gRPC-Web request gets `415`.

The correctness of the emitted framing (echo faithful + trailer marked + status OK) and the
HTTP wrapping (the frame bytes are a suffix of the served response) are proven in
`Proto.GrpcWebProven`; a Lean driver (`Reactor.GrpcWebDrive`) exercises the compiled
`drorbServeGrpcWeb` on a real gRPC-Web request and prints the framed response.

Export: `@[export drorb_serve_grpcweb]` — same `ByteArray → ByteArray` ABI as `drorb_serve`,
so a host `DRORB_SPAN` seam (fragment supplied to the dataplane lane) can select it.
-/
import Reactor.Proxy.Grpc
import Reactor.Serialize

namespace Reactor.GrpcWebServe

open Reactor.Proxy.Grpc

/-! ## Byte bridges (the codec is `List Nat`; the serializer is `List UInt8`) -/

/-- Lower a list of byte-valued naturals to `UInt8` bytes. -/
def natsToBytes (l : List Nat) : List UInt8 := l.map (fun n => UInt8.ofNat n)

/-- ASCII bytes of a string, as `List Nat` (for the trailer block, at the codec level). -/
def strToNats (s : String) : List Nat := s.toUTF8.toList.map (fun b => b.toNat)

/-! ## The gRPC-Web response body -/

/-- The trailer block of a successful unary call: `grpc-status:0` + CRLF (gRPC-Web
delivers trailers in the body, as `name:value\r\n`). -/
def okTrailerBlock : List Nat := strToNats "grpc-status:0\r\n"

/-- The gRPC-Web response body for a unary echo of `payload`: a single uncompressed
data frame carrying `payload`, then the `0x80` trailer frame carrying `grpc-status:0`. -/
def grpcWebBody (payload : List Nat) : List Nat :=
  buildGrpcWebResponse (encodeFrame { compressed := false, payload := payload }) okTrailerBlock

/-! ## The served HTTP/1.1 response -/

/-- `Content-Type` header name (ASCII bytes). -/
def ctName : List UInt8 := "Content-Type".toUTF8.toList
/-- gRPC-Web binary content type. -/
def ctVal : List UInt8 := "application/grpc-web+proto".toUTF8.toList

/-- The full `200` gRPC-Web response for a unary echo of `payload`, built with the
DEPLOYED response serializer's record (so `Content-Length` is fixed to the body length). -/
def grpcWebResponse (payload : List Nat) : _root_.Reactor.Response :=
  { status := 200
    reason := "OK".toUTF8.toList
    headers := [(ctName, ctVal)]
    body := natsToBytes (grpcWebBody payload) }

/-- The `415` response for a request that is not gRPC-Web. -/
def unsupportedResponse : _root_.Reactor.Response :=
  _root_.Reactor.error4xx 415 "Unsupported Media Type".toUTF8.toList []

/-! ## Request recognition + body extraction (HTTP/1.1) -/

/-- Is `p` a prefix of `l`? -/
def isPrefixB (p l : List UInt8) : Bool := p == l.take p.length

/-- Does `needle` occur as a contiguous infix of `hay`? -/
def hasInfix (needle hay : List UInt8) : Bool :=
  match hay with
  | [] => needle.isEmpty
  | _ :: t => isPrefixB needle hay || hasInfix needle t

/-- A request is gRPC-Web iff its bytes contain the `application/grpc-web` media type. -/
def isGrpcWebReq (input : List UInt8) : Bool :=
  hasInfix ("application/grpc-web".toUTF8.toList) input

/-- Drop the request head, returning the bytes after the first CRLF-CRLF (the body). -/
def afterHeaders : List UInt8 → List UInt8
  | 13 :: 10 :: 13 :: 10 :: rest => rest
  | _ :: rest => afterHeaders rest
  | [] => []

/-- The echoed message payload: the payload of the leading gRPC frame in the request
body (empty if absent/malformed). -/
def echoPayload (bytes : List UInt8) : List Nat :=
  match decodeFrame ((afterHeaders bytes).map (fun b => b.toNat)) with
  | some (f, _) => f.payload
  | none => []

/-! ## The deployed export -/

/-- **The gRPC-Web unary serve** (`drorb_serve_grpcweb`). A gRPC-Web request is answered
`200` with the echo data frame + `grpc-status:0` trailer frame; anything else gets `415`.
Same `ByteArray → ByteArray` ABI as `drorb_serve`. -/
@[export drorb_serve_grpcweb]
def drorbServeGrpcWeb (input : ByteArray) : ByteArray :=
  if isGrpcWebReq input.toList then
    ByteArray.mk (_root_.Reactor.serialize (grpcWebResponse (echoPayload input.toList))).toArray
  else
    ByteArray.mk (_root_.Reactor.serialize unsupportedResponse).toArray

end Reactor.GrpcWebServe
