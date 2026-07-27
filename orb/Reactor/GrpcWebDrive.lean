/-
# Reactor.GrpcWebDrive — drive the compiled gRPC-Web serve on a real request

Exercises `@[export drorb_serve_grpcweb]` end-to-end: feeds a real gRPC-Web unary request
(`POST` a length-prefixed `"hi"`), then decodes the served response to show the echoed
data frame and the `grpc-status:0` trailer frame — the SEEN framed response.
-/
import Reactor.GrpcWebServe

open Reactor.Proxy.Grpc
open Reactor.GrpcWebServe

private def reqHead : String :=
  "POST /echo.Echo/Say HTTP/1.1\r\nContent-Type: application/grpc-web+proto\r\n\r\n"
private def reqFrame : List Nat := encodeFrame { compressed := false, payload := [104, 105] }
private def req : ByteArray := ByteArray.mk (reqHead.toUTF8.toList ++ natsToBytes reqFrame).toArray

def main : IO Unit := do
  let out := (drorbServeGrpcWeb req).toList
  IO.println s!"[grpcweb-drive] request is gRPC-Web: {isGrpcWebReq req.toList}"
  IO.println s!"[grpcweb-drive] response {out.length} bytes"
  IO.println s!"[grpcweb-drive] status line: {String.mk ((out.takeWhile (fun b => b != 13)).map (fun b => Char.ofNat b.toNat))}"
  let body := afterHeaders out
  IO.println s!"[grpcweb-drive] body bytes (nats): {body.map (fun b => b.toNat)}"
  match decodeFrame (body.map (fun b => b.toNat)) with
  | some (f, tail) =>
      IO.println s!"[grpcweb-drive] echoed data-frame payload (nats): {f.payload}"
      IO.println s!"[grpcweb-drive] payload as text: {String.mk (f.payload.map (fun n => Char.ofNat n))}"
      IO.println s!"[grpcweb-drive] trailer frame flag=0x80 marked: {isTrailerFrame (tail.headD 0)}"
      IO.println s!"[grpcweb-drive] trailer bytes as text: {String.mk ((tail.drop 5).map (fun n => Char.ofNat n))}"
  | none => IO.println "[grpcweb-drive] DECODE FAILED"
