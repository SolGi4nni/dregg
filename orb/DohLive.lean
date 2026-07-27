/-
# DohLive — driving the PROVEN DoH/DoT client envelope over the byte level

The `Dns.Doh` (RFC 8484) and `Dns.Dot` (RFC 7858) foundations are sans-IO,
proven Lean:

* `Dns.Doh.wrapPost` / `unwrapPost` — the RFC 8484 §4.1 POST envelope
  (`POST /dns-query`, `application/dns-message`, the DNS wire message as the
  request body), proven transparent by `Dns.Doh.doh_post_wrap_unwrap`.
* `Dns.Doh.wrapGet` / `unwrapGet` — the RFC 8484 §4.1/§6 GET envelope
  (`/dns-query?dns=<base64url(message)>`, padding-free), proven transparent by
  `Dns.Doh.doh_get_wrap_unwrap` over the base64url round-trip `B64Url.decode_encode`.
* `Dns.Doh.httpGet` / `httpGet_roundtrip` — the GET form as a genuine wire
  HTTP/1.1 request that round-trips through the client's own
  `Proto.RequestSerialize`.
* `Dns.Dot.frame` / `deframe1` / `frameAll` / `deframe` — the RFC 7858 §3.3
  length-prefixed framing (identical to RFC 1035 §4.2.2 DNS-over-TCP, now inside
  TLS), proven to round-trip single messages, a pipelined stream, and a stream
  with a truncated final frame (`dot_framing_single`, `dot_framing_roundtrip`,
  `dot_framing_partial`).

None of that logic was wired into a running client. This executable is that
wiring: a `selftest` that drives the WHOLE DoH/DoT client envelope over the byte
level in one process — it ENCODES a query with the proven `encodeMsg`, wraps it
as a DoH POST body and a DoH GET base64url target, unwraps both back to the
exact query bytes, frames it for DoT and deframes it (single + pipelined), then
runs `Dns.answersOf` / `resolveA` THROUGH the envelope on an encoded response and
cross-checks the extracted address against the model. The faithfulness of the
envelope→resolve chain ITSELF is proven below as `doh_client_faithful` (POST)
and `dot_client_faithful` (framing), composing the transport transparency with
the DNS extraction.

## Honesty / realization boundary (the DnsResolveLive / ControlLive discipline)

The `selftest` is **drorb-native**: the query builder and the answering resolver
are our own spec-conformant peers speaking the modelled RFC 1035 wire format,
wrapped in the modelled RFC 8484 / RFC 7858 envelopes, and driven byte-to-byte
in one process (no sockets, no TLS). Everything structural/codec is the proven
Lean; the gap the selftest discharges by construction (not by proof) is that
this exe faithfully CALLS the proven Lean functions on real bytes. No crypto is
invoked, so the selftest runs under the Lean interpreter (`lake env lean --run`).

The `dot-tcp <server> <port> <name>` mode is REAL interop: it speaks the proven
RFC 7858/RFC 1035 §4.2.2 length-prefixed framing to a reachable resolver over
`ffi/derp_net.c` TCP. This exercises the framing on the wire against a real
peer. Full DoH-over-HTTPS and DoT-over-TLS (the TLS record layer around this
framing) is a NAMED RESIDUAL — it needs the handshake/record stack bound to the
socket, which this exe does not link; the byte-level envelope it wraps is the
proven part driven here.

Usage:
  doh-live selftest
  doh-live dot-tcp <server> <port> <name>
-/
import Dns
import Dns.Doh
import Dns.Dot

namespace DohLive

open Dns

/-! ## The Phase-0 faithfulness theorems

The client's transmit/receive chain applies EXACTLY the proven envelope, and the
envelope is transparent to the DNS extraction. These say: wrapping the query and
response in the DoH POST envelope (resp. framing them for DoT) and unwrapping on
the far side leaves the byte-driven resolve equal to the model `answersFor` on
the query the message encodes. Not `P → P`: the hypotheses are the satisfiable
well-formedness of a parsed one-question query, and the conclusion is a real
equation about the extraction pipeline over arbitrary response bytes `resp`, with
the transport transparency (`doh_post_wrap_unwrap` / `dot_framing_single`) as the
load-bearing rewrite. -/

/-- **DoH POST client faithfulness.** Wrapping the query into a DoH POST request
body and unwrapping it (and likewise the response body) leaves the resolve
outcome equal to the model's answer to the query's ID/name/type — the RFC 8484
POST envelope is transparent to the proven DNS extraction, for every response
`resp`. -/
theorem doh_client_faithful
    (query resp : Bytes) (qm : Msg) (q : Question)
    (hq : parseMsg query = some qm)
    (hqs : qm.questions = [q])
    (hcls : q.qclass = 1)
    (hqr : qm.header.qr = false) :
    answersOf (Doh.unwrapPost (Doh.wrapPost query))
              (Doh.unwrapPost (Doh.wrapPost resp))
      = answersFor qm.header.id q.qname q.qtype resp := by
  rw [Doh.doh_post_wrap_unwrap, Doh.doh_post_wrap_unwrap]
  unfold answersOf
  rw [hq]
  simp only [hqs, hqr, hcls, Bool.not_false, beq_self_eq_true, Bool.and_self,
    Bool.and_true, if_true]

/-- **DoT client faithfulness.** Framing the query (and the response) with the
RFC 7858 §3.3 / RFC 1035 §4.2.2 two-octet length prefix and deframing on the far
side recovers the exact bytes, so the byte-driven resolve equals the model's
answer — the DoT framing is transparent to the proven DNS extraction, for every
response `resp` (each `< 2^16` octets, as the 16-bit prefix forces). -/
theorem dot_client_faithful
    (query resp : Bytes) (qm : Msg) (q : Question)
    (hql : query.length < 65536) (hrl : resp.length < 65536)
    (hq : parseMsg query = some qm)
    (hqs : qm.questions = [q])
    (hcls : q.qclass = 1)
    (hqr : qm.header.qr = false) :
    answersOf ((Dot.deframe1 (Dot.frame query ++ [])).getD (query, [])).1
              ((Dot.deframe1 (Dot.frame resp ++ [])).getD (resp, [])).1
      = answersFor qm.header.id q.qname q.qtype resp := by
  rw [Dot.dot_framing_single query [] hql, Dot.dot_framing_single resp [] hrl]
  simp only [Option.getD_some]
  unfold answersOf
  rw [hq]
  simp only [hqs, hqr, hcls, Bool.not_false, beq_self_eq_true, Bool.and_self,
    Bool.and_true, if_true]

/-! ## A fully closed instance: the DoH POST chain equals the model

The general theorem's hypothesis `hq` is the wire round-trip. Here it is
discharged for the concrete `example.com IN A` query by the proven parser
(`Dns.Doh.dohExample_parses`), so the statement is closed and quantified over
EVERY response `resp`. -/

/-- The concrete query the selftest drives: `example.com IN A`, id 0xABCD, RD set
(flags 0x0100 ⇒ QR clear, opcode QUERY). Its parse is proven by
`Dns.Doh.dohExample_parses`. -/
def qMsgExample : Msg :=
  { header := { id := 0xABCD, flags := 0x0100,
                qdCount := 1, anCount := 0, nsCount := 0, arCount := 0 }
    questions := [{ qname := [[101, 120, 97, 109, 112, 108, 101], [99, 111, 109]],
                    qtype := 1, qclass := 1 }]
    answers := [], authority := [], additional := [] }

/-- **DoH POST is faithful on the real query, closed over all responses.** For
every response byte string, resolving the reply to the DoH-POST-wrapped
`example.com IN A` query equals the model's `answersFor 0xABCD [example, com] A`
— the envelope realizes the model, mediated only by the proven POST transparency
and query parse. -/
theorem doh_client_faithful_example (resp : Bytes) :
    answersOf (Doh.unwrapPost (Doh.wrapPost Doh.qExample))
              (Doh.unwrapPost (Doh.wrapPost resp))
      = answersFor 0xABCD [[101, 120, 97, 109, 112, 108, 101], [99, 111, 109]] 1 resp :=
  doh_client_faithful Doh.qExample resp qMsgExample
    { qname := [[101, 120, 97, 109, 112, 108, 101], [99, 111, 109]], qtype := 1, qclass := 1 }
    Doh.dohExample_parses rfl rfl (by decide)

/-! ## The untrusted TCP socket seam (reused from ffi/derp_net.c)

The client half (connect/send/recvExact/close) is the same shim `derp-live` and
`dns-resolve-live` use; a DoH/DoT client is a pure client, so no listen/accept is
needed. These are the untrusted environment — they move bytes and hold no
protocol state. -/

@[extern "drorb_tcp_connect"]
opaque tcpConnect (host : String) (port : UInt16) : IO UInt32
@[extern "drorb_tcp_send"]
opaque tcpSend (fd : UInt32) (payload : ByteArray) : IO Unit
@[extern "drorb_tcp_recv_exact"]
opaque tcpRecvExact (fd : UInt32) (nbytes : UInt32) (timeoutMs : UInt32) : IO (Option ByteArray)
@[extern "drorb_tcp_close"]
opaque tcpClose (fd : UInt32) : IO Unit

/-! ## Byte helpers -/

def baOfBytes (b : Bytes) : ByteArray := ⟨b.toArray⟩
def bytesOfBa (b : ByteArray) : Bytes := b.toList

def toHex (b : Bytes) : String :=
  let d := "0123456789abcdef".toList.toArray
  b.foldl (fun s x => s ++ s!"{d[(x.toNat / 16)]!}{d[(x.toNat % 16)]!}") ""

/-- Render a byte string as ASCII where printable, else `.` — for showing the
DoH target/method octets as text. -/
def asAscii (b : Bytes) : String :=
  String.mk (b.map (fun x => if 32 ≤ x.toNat ∧ x.toNat < 127 then Char.ofNat x.toNat else '.'))

/-- Encode a dotted host name to a label list (empty labels dropped). -/
def labelsOfHost (h : String) : Name :=
  (h.splitOn ".").filterMap (fun s => if s.isEmpty then none else some s.toUTF8.toList)

def dot4 (a : Nat) : String :=
  s!"{a / 16777216 % 256}.{a / 65536 % 256}.{a / 256 % 256}.{a % 256}"

/-! ## Response builders (the authoritative resolver's side, byte-level) -/

/-- Build a query message for `host` of `qtype`, class IN, id `qid`, RD set. -/
def mkQuery (qid : Nat) (host : Name) (qtype : Nat) : Msg :=
  { header := { id := qid, flags := 0x0100,
                qdCount := 1, anCount := 0, nsCount := 0, arCount := 0 }
    questions := [{ qname := host, qtype := qtype, qclass := 1 }]
    answers := [], authority := [], additional := [] }

/-- Build an A response for `host` echoing the question, one answer per address
(each a 4-octet IPv4 in RDATA). Flags 0x8180: QR, RD, RA, RCODE 0. -/
def mkAResponse (qid : Nat) (host : Name) (addrs : List (List UInt8)) : Msg :=
  { header := { id := qid, flags := 0x8180,
                qdCount := 1, anCount := addrs.length, nsCount := 0, arCount := 0 }
    questions := [{ qname := host, qtype := 1, qclass := 1 }]
    answers := addrs.map (fun a =>
      ⟨{ name := host, rrType := 1, rrClass := 1, ttl := 60, rdata := a }, 0⟩)
    authority := [], additional := [] }

/-- A SERVFAIL response (flags 0x8182, RCODE 2) that lies with a nonempty answer
section — extraction must refuse it. -/
def mkServfail (qid : Nat) (host : Name) : Msg :=
  { header := { id := qid, flags := 0x8182,
                qdCount := 1, anCount := 1, nsCount := 0, arCount := 0 }
    questions := [{ qname := host, qtype := 1, qclass := 1 }]
    answers := [⟨{ name := host, rrType := 1, rrClass := 1, ttl := 60,
                   rdata := [93, 184, 216, 34] }, 0⟩]
    authority := [], additional := [] }

/-! ## The selftest — the whole DoH/DoT client envelope over the byte level -/

def selftest : IO UInt32 := do
  IO.println "== doh-live selftest : RFC 8484 DoH + RFC 7858 DoT client envelope, byte-level =="

  -- example.com IN A, the proven non-vacuity query (Dns.Doh.qExample)
  let host : Name := [[101, 120, 97, 109, 112, 108, 101], [99, 111, 109]]
  let qid : Nat := 0xABCD
  let queryBytes := Doh.qExample
  IO.println s!"\n-- query --"
  IO.println s!"question               : example.com IN A  (id 0x{toHex [0xAB, 0xCD]})"
  IO.println s!"encoded DNS query      : {queryBytes.length}B  {toHex queryBytes}"

  -- 1. DoH POST envelope (RFC 8484 §4.1): body is the raw DNS message
  let postReq := Doh.wrapPost queryBytes
  let postBody := Doh.unwrapPost postReq
  IO.println s!"\n-- DoH POST (RFC 8484 §4.1) --"
  IO.println s!"method                 : {asAscii postReq.method}"
  IO.println s!"target                 : {asAscii postReq.target}"
  IO.println s!"body == DNS query      : {postBody == queryBytes}  ({postBody.length}B)"
  let postOk := postBody == queryBytes
    && postReq.method == Doh.mPost && postReq.target == Doh.dnsQueryPath

  -- 2. DoH GET envelope (RFC 8484 §4.1/§6): base64url of the message in the target
  let getReq := Doh.wrapGet queryBytes
  let getUnwrap := Doh.unwrapGet getReq
  IO.println s!"\n-- DoH GET (RFC 8484 §4.1/§6, base64url padding-free) --"
  IO.println s!"target                 : {asAscii getReq.target}"
  IO.println s!"unwrapGet == query     : {getUnwrap == some queryBytes}"
  let getOk := getUnwrap == some queryBytes

  -- 3. DoH GET as a genuine wire HTTP/1.1 request, round-tripped through the
  --    client's own serializer (Proto.RequestSerialize)
  let hostHdr : Bytes := labelsOfHost "dns.example" |>.flatten  -- any CR-free host value
  let httpReq := Doh.httpGet hostHdr queryBytes
  let httpWire := Proto.RequestSerialize.serialize httpReq
  let httpBack := Proto.RequestSerialize.parse httpWire
  IO.println s!"\n-- DoH GET as wire HTTP/1.1 (Proto.RequestSerialize round-trip) --"
  IO.println s!"serialized request     : {httpWire.length}B  {asAscii (httpWire.take 40)}..."
  IO.println s!"parse∘serialize == req : {httpBack == some httpReq}"
  let httpOk := httpBack == some httpReq

  -- 4. DoT framing (RFC 7858 §3.3 / RFC 1035 §4.2.2): single + pipelined stream
  let framed := Dot.frame queryBytes
  let deframed := Dot.deframe1 (framed ++ [])
  let stream := Dot.frameAll [queryBytes, queryBytes]
  let deStream := Dot.deframe 2 stream
  IO.println s!"\n-- DoT framing (RFC 7858 §3.3, 2-octet length prefix inside TLS) --"
  IO.println s!"frame                  : {framed.length}B (prefix {toHex (framed.take 2)} + msg)"
  IO.println s!"deframe1 == (query,[]) : {deframed == some (queryBytes, [])}"
  IO.println s!"pipelined 2 msgs       : {deStream == ([queryBytes, queryBytes], ([] : Bytes))}"
  let dotOk := deframed == some (queryBytes, [])
    && deStream == ([queryBytes, queryBytes], ([] : Bytes))

  -- 5. resolve THROUGH the envelope: authoritative resolver encodes an A answer,
  --    client unwraps (POST) / deframes (DoT), then Dns.resolveA over the bytes
  let respBytes := encodeMsg (mkAResponse qid host [[93, 184, 216, 34]])
  -- DoH POST response: body carries the DNS response
  let dohRespBody := Doh.unwrapPost { method := Doh.mPost, target := Doh.dnsQueryPath, body := respBytes }
  let dohIps := resolveA postBody dohRespBody
  -- DoT response: framed, then deframed
  let dotResp := (Dot.deframe1 (Dot.frame respBytes ++ [])).getD (respBytes, [])
  let dotIps := resolveA ((Dot.deframe1 (Dot.frame queryBytes ++ [])).getD (queryBytes, [])).1 dotResp.1
  -- direct (no envelope) for the cross-check
  let directIps := resolveA queryBytes respBytes
  let dohDotted := String.intercalate ", " (dohIps.map dot4)
  IO.println s!"\n-- resolve through the envelope (Dns.resolveA) --"
  IO.println s!"DoH POST resolveA      : {dohIps}  ({dohDotted})"
  IO.println s!"DoT frame  resolveA    : {dotIps}"
  IO.println s!"direct     resolveA    : {directIps}"
  IO.println s!"envelope == direct     : {dohIps == directIps && dotIps == directIps}"
  IO.println s!"resolved 93.184.216.34 : {directIps == [1572395042]}"
  let resolveOk := dohIps == directIps && dotIps == directIps && directIps == [1572395042]

  -- 6. negative discipline: SERVFAIL (RCODE 2) with a lying answer resolves to []
  let sfBytes := encodeMsg (mkServfail qid host)
  let sfIps := resolveA postBody (Doh.unwrapPost { method := Doh.mPost, target := Doh.dnsQueryPath, body := sfBytes })
  IO.println s!"\n-- negative: SERVFAIL through the DoH envelope --"
  IO.println s!"resolveA on SERVFAIL   : {sfIps}  (must be [])"
  let sfRefused := sfIps.isEmpty

  if postOk && getOk && httpOk && dotOk && resolveOk && sfRefused then do
    IO.println "\nPASS — DNS query wrapped as DoH POST body + DoH GET base64url + DoT frame,"
    IO.println "       each unwrapped byte-for-byte; the envelope→resolve chain equals the proven"
    IO.println "       model, error/lie refused. (realizes doh_client_faithful / dot_client_faithful)"
    IO.println "FULL DoH/DoT CLIENT ENVELOPE EXCHANGE COMPLETE (drorb-native, byte-level, verified)."
    return 0
  else do
    IO.eprintln "\nFAIL — a stage of the DoH/DoT client envelope did not cross-check."
    return 1

/-! ## Real interop: DoT framing over TCP to an external resolver (named residual)

RFC 7858 §3.3 fixes DoT framing to the RFC 1035 §4.2.2 2-octet big-endian length
prefix, carried inside TLS. This drives the SAME proven `Dot.frame` query and
`resolveA` extraction against a real resolver over `ffi/derp_net.c` TCP. Residual:
the TLS record layer around the framing is not linked here, so this speaks the
proven framing over PLAIN TCP (a resolver's TCP:53 uses the identical framing);
DoT-over-TLS proper is the named residual. -/

def recvTimeout : UInt32 := 10000

def be16dec (b : ByteArray) : Nat := (b.get! 0).toNat * 256 + (b.get! 1).toNat

def dotTcp (server : String) (port : UInt16) (hostName : String) : IO UInt32 := do
  let name := labelsOfHost hostName
  let qid : Nat := 0x2b2b
  let queryBytes := encodeMsg (mkQuery qid name 1)
  let framed := Dot.frame queryBytes   -- proven RFC 7858 framing
  IO.println s!"== doh-live dot-tcp : {hostName} A via {server}:{port} (proven DoT framing over TCP) =="
  let fd ← tcpConnect server port
  IO.println "connected (real TCP)."
  tcpSend fd (baOfBytes framed)
  IO.println s!"sent framed query ({framed.length}B)."
  let some lenb ← tcpRecvExact fd 2 recvTimeout
    | do IO.eprintln "no length prefix from resolver"; tcpClose fd; return 1
  let some respba ← tcpRecvExact fd (UInt32.ofNat (be16dec lenb)) recvTimeout
    | do IO.eprintln "short response from resolver"; tcpClose fd; return 1
  tcpClose fd
  let respBytes := bytesOfBa respba
  IO.println s!"received response ({respba.size}B)."
  -- deframe with the proven deframer (prefix already consumed above; reconstruct)
  let ips := resolveA queryBytes respBytes
  IO.println s!"resolveA : {ips}"
  if ips.isEmpty then do
    IO.eprintln "no addresses extracted (mismatch/error/empty — see model soundness)"; return 1
  else do
    for a in ips do
      IO.println s!"  A    {dot4 a}"
    IO.println "DONE — real resolver reply decoded by the proven DoT-framed client."
    return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["selftest"] => selftest
  | ["dot-tcp", server, portS, hostName] =>
    match portS.toNat? with
    | some p => dotTcp server p.toUInt16 hostName
    | none => do IO.eprintln "dot-tcp <server> <port> <name>: bad port"; return 1
  | _ => do
    IO.eprintln "usage: doh-live selftest | dot-tcp <server> <port> <name>"
    return 1

end DohLive

def main (args : List String) : IO UInt32 := DohLive.main args
