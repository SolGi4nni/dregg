import Proto.RequestSerialize

/-!
# The verified HTTP/1.1 client transaction

A client transaction is: **serialize a request → (send over the wire) → parse
the response.** This module models the transaction as a sans-IO function and
proves its end-to-end faithfulness over a loopback — the composition of the two
proven round-trips:

* the request the client emits is exactly the request the peer parses
  (`Proto.RequestSerialize.parse_serialize`); and
* the response the peer emits is exactly the response the client parses
  (`Proto.ResponseParse.parse_serialize`).

So a client speaking to a drorb-shaped server (or a drorb server speaking to a
drorb client) agree on every byte in both directions.

## What is proven

`transaction_faithful` — for a well-formed request and a handler that always
produces well-formed responses, the client transaction yields exactly the wire
form of the handler's response applied to the request the client sent:

    transaction handler req = some (ResponseParse.wireForm (handler req))

`transaction_ok200` witnesses it on a concrete `GET / HTTP/1.1` against a
`200 OK` echo handler.

0 sorries; axioms ⊆ `{propext, Quot.sound, Classical.choice}`.
-/

namespace Proto
namespace Client
namespace H1

open Reactor (Response serialize)

abbrev Bytes := List UInt8

/-- One HTTP/1.1 client transaction over a loopback. The client serializes
`req` and puts the bytes on the wire; the peer parses them, applies `handler`,
and serializes the response back; the client parses the returned bytes. The two
serialize/parse hops are the server's (request) and the client's (response). -/
def transaction (handler : Proto.Request → Response) (req : Proto.Request) : Option Response :=
  match RequestSerialize.parse (RequestSerialize.serialize req) with
  | none => none
  | some peerReq => ResponseParse.parse (serialize (handler peerReq))

/-- **End-to-end faithfulness.** For a well-formed request and a handler that
always yields well-formed responses, the client recovers exactly the wire form
of the handler's response to the request it actually sent — every byte agrees in
both directions. -/
theorem transaction_faithful
    (handler : Proto.Request → Response) (req : Proto.Request)
    (hreq : RequestSerialize.WF req)
    (hresp : ∀ r, ResponseParse.WF (handler r)) :
    transaction handler req = some (ResponseParse.wireForm (handler req)) := by
  unfold transaction
  rw [RequestSerialize.parse_serialize req hreq]
  exact ResponseParse.parse_serialize (handler req) (hresp req)

/-- A `200 OK` echo handler: always well-formed (no caller headers, `OK` reason). -/
def echoOk (_ : Proto.Request) : Response := Reactor.ok200 [104, 105]  -- body "hi"

theorem echoOk_WF (r : Proto.Request) : ResponseParse.WF (echoOk r) :=
  ResponseParse.ok200_WF _

/-- The transaction, discharged concretely: a `GET / HTTP/1.1` client request
against the `200 OK` echo handler round-trips end to end. -/
theorem transaction_ok200 :
    transaction echoOk RequestSerialize.getExample
      = some (ResponseParse.wireForm (echoOk RequestSerialize.getExample)) :=
  transaction_faithful echoOk _ RequestSerialize.getExample_WF echoOk_WF

/-! ## The C ABI seam the outbound (client) host calls -/

/-- **`drorb_response_parse` — the verified response parser as a
`ByteArray → ByteArray`.** Input: the raw bytes of an upstream HTTP/1.1 response.
Output on success: `1 :: <decimal status bytes> :: 0 :: <body bytes>` (the client
reads a real numeric status via the proven decimal inverse, then the body); on a
parse failure: the single byte `0`. This is the outbound dual of the server's
`drorb_serve`: the host dials the upstream, writes the serialized request, reads
the response bytes, and crosses this seam to parse them as a verified client. -/
@[export drorb_response_parse]
def responseParseC (input : ByteArray) : ByteArray :=
  match ResponseParse.parse input.toList with
  | none => ⟨#[0]⟩
  | some resp => ⟨((1 : UInt8) :: (Reactor.natToDec resp.status ++ (0 : UInt8) :: resp.body)).toArray⟩

/-- **`drorb_request_serialize` — the verified request serializer as a
`ByteArray → ByteArray`.** Input framing: `mLen :: method :: tLen :: target ::
vLen :: version` (each length a single byte for the fixed request-line fields);
output: the wire bytes of the request line + blank line (no headers). The host
puts these bytes on the wire toward the upstream. Empty input ⇒ empty output. -/
@[export drorb_request_serialize]
def requestSerializeC (input : ByteArray) : ByteArray :=
  let l := input.toList
  match l with
  | mLen :: rest =>
    let method := rest.take mLen.toNat
    let rest := rest.drop mLen.toNat
    match rest with
    | tLen :: rest =>
      let target := rest.take tLen.toNat
      let rest := rest.drop tLen.toNat
      match rest with
      | vLen :: rest =>
        let version := rest.take vLen.toNat
        ⟨(RequestSerialize.serialize
            { method := method, target := target, version := version, headers := [] }).toArray⟩
      | [] => ⟨#[]⟩
    | [] => ⟨#[]⟩
  | [] => ⟨#[]⟩

end H1
end Client
end Proto
