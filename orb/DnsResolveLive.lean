/-
# DnsResolveLive — driving the PROVEN DNS resolver over the byte level

The `Dns` foundation is sans-IO, proven Lean: the RFC 1035 §4.1 whole-message
parse (`Dns.parseMsg`) with RDATA offsets, the §4.1 encoders
(`Dns.encodeName` / `encodeQuestion` / `encodeRR` / `encodeMsg`) pinned to that
parser by round-trip theorems (`decodeName_encodeName_at`,
`parseHeader_encodeHeader`, and the kernel-checked whole-message vectors), and
the extraction layer (`Dns.answersOf` / `answersFor` / `resolveA` / `resolveAAAA`)
that decides what a response *answers*: §7.3 response matching (ID, QR, opcode,
TC, the RFC 6891 §6.1.3 EDNS extended RCODE), the §3.3.1 CNAME chase, and the
whole-section scan — each with its soundness theorem (`answersFor_sound`,
`collect_sound`, `answersFor_rcode`, `answersFor_tc`, `answersFor_id`, …).

None of that logic was wired into a running binary. This executable is that
wiring: a `selftest` that drives the WHOLE resolver over the byte level in one
process — it ENCODES a query with the proven `encodeMsg`, has an authoritative
resolver ENCODE a response, then runs `Dns.answersOf` / `resolveA` on the two
byte strings and cross-checks the result against the model. It also carries a
`resolve` mode that speaks real DNS-over-TCP (RFC 1035 §4.2.2, 2-octet length
prefix) to any reachable resolver over `ffi/derp_net.c`.

## Honesty / realization boundary (the DiscoLive / ControlLive discipline)

The `selftest` is **drorb-native**: both the query builder and the answering
resolver are our own spec-conformant peers speaking the modelled RFC 1035 wire
format, driven byte-to-byte in one process (no sockets). Everything
structural/codec is the proven Lean; the gap the selftest discharges by
construction (not by proof) is that this exe faithfully CALLS the proven Lean
functions on real bytes. The faithfulness of the decode→resolve chain ITSELF is
proven below as `dns_resolve_faithful` (composing the wire-codec round-trip with
the extraction). The `resolve <server> <port> <name>` mode is REAL interop with
an external resolver over TCP — a named residual, since it needs a reachable
DNS server and DNS-over-TCP support.

Usage:
  dns-resolve-live selftest
  dns-resolve-live resolve <server> <port> <name> [qtype]
-/
import Dns

namespace DnsResolveLive

open Dns

/-! ## The Phase-0 faithfulness theorem

The running loop's decode→resolve chain applies EXACTLY the proven extraction.
A resolver holds only the query bytes it sent and the response bytes it
received; `answersOf` re-parses the query to recover its ID/name/type and then
extracts. This theorem says: parsing the query bytes back and resolving equals
resolving directly with the model parameters the query encodes — the byte-driven
resolve realizes the model `answersFor`. It composes the query wire round-trip
(`hq : parseMsg query = some qm`, realized at run time and witnessed by the
`decide` round-trip below) with the definitional extraction. Not a `P → P`: the
hypotheses are the satisfiable well-formedness of a parsed one-question query
(the selftest's query satisfies them), and the conclusion is a real equation
about the extraction pipeline over arbitrary response bytes `resp`. -/
theorem dns_resolve_faithful
    (query resp : Bytes) (qm : Msg) (q : Question)
    (hq : parseMsg query = some qm)
    (hqs : qm.questions = [q])
    (hcls : q.qclass = 1)
    (hqr : qm.header.qr = false) :
    answersOf query resp = answersFor qm.header.id q.qname q.qtype resp := by
  unfold answersOf
  rw [hq]
  simp only [hqs, hqr, hcls, Bool.not_false, beq_self_eq_true, Bool.and_self,
    Bool.and_true, if_true]

/-! ## A fully closed instance: the ENCODE→resolve chain equals the model

The general theorem's hypothesis `hq` is the wire round-trip. Here it is
discharged for a concrete query by the proven encoder/parser (`decide` runs the
REAL `encodeMsg`/`parseMsg`), so the statement is closed and quantified over
EVERY response `resp`: encoding the query with `encodeMsg`, sending it, and
resolving the reply with `answersOf` yields PRECISELY the model's answer to the
query's ID/name/type. This is the direct analogue of ControlLive's
`control_applies_netmap_faithfully`. -/

/-- The concrete query the selftest drives: `up IN A`, id 0x1234, RD set
(flags 0x0100 ⇒ QR clear, opcode QUERY). -/
def queryUpMsg : Msg :=
  { header := { id := 0x1234, flags := 0x0100,
                qdCount := 1, anCount := 0, nsCount := 0, arCount := 0 }
    questions := [{ qname := [[117, 112]], qtype := 1, qclass := 1 }]
    answers := [], authority := [], additional := [] }

/-- The query wire round-trip, realized: what `encodeMsg` writes, `parseMsg`
reads back verbatim — the REAL codecs run by the kernel. -/
theorem queryUp_roundtrip : parseMsg (encodeMsg queryUpMsg) = some queryUpMsg := by
  decide

/-- **Encode→resolve is faithful, closed over all responses.** For every
response byte string, resolving the reply to the `encodeMsg`-encoded `up IN A`
query equals the model's `answersFor 0x1234 [up] A` — the wire realizes the
model, mediated only by the proven query round-trip. -/
theorem dns_resolve_faithful_up (resp : Bytes) :
    answersOf (encodeMsg queryUpMsg) resp
      = answersFor 0x1234 [[117, 112]] 1 resp :=
  dns_resolve_faithful (encodeMsg queryUpMsg) resp queryUpMsg
    { qname := [[117, 112]], qtype := 1, qclass := 1 }
    queryUp_roundtrip rfl rfl (by decide)

/-! ## The untrusted TCP socket seam (reused from ffi/derp_net.c)

The client half (connect/send/recvExact/close) is the same shim `derp-live`
uses; a resolver is a pure client, so no listen/accept is needed. These are the
untrusted environment — they move bytes and hold no protocol state. -/

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

/-- Render a decoded name (label list) as dotted text where the labels are
UTF-8, else hex. -/
def nameStr (n : Name) : String :=
  String.intercalate "." (n.map (fun l => (String.fromUTF8? ⟨l.toArray⟩).getD (toHex l)))

/-- Encode a dotted host name to a label list (empty labels dropped). -/
def labelsOfHost (h : String) : Name :=
  (h.splitOn ".").filterMap (fun s => if s.isEmpty then none else some s.toUTF8.toList)

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

/-- A SERVFAIL response (flags 0x8182, RCODE 2) that lies with a nonempty
answer section — extraction must refuse it. -/
def mkServfail (qid : Nat) (host : Name) : Msg :=
  { header := { id := qid, flags := 0x8182,
                qdCount := 1, anCount := 1, nsCount := 0, arCount := 0 }
    questions := [{ qname := host, qtype := 1, qclass := 1 }]
    answers := [⟨{ name := host, rrType := 1, rrClass := 1, ttl := 60,
                   rdata := [93, 184, 216, 34] }, 0⟩]
    authority := [], additional := [] }

def dot (a : List UInt8) : String :=
  String.intercalate "." (a.map (fun b => toString b.toNat))

/-! ## The selftest — the whole resolver over the byte level, one process -/

def selftest : IO UInt32 := do
  IO.println "== dns-resolve-live selftest : RFC 1035 resolver, byte-level, encode + resolve =="

  let host : Name := [[117, 112]]  -- "up"
  let qid : Nat := 0x1234

  -- 1. build + ENCODE the query with the proven encoder
  let qMsg := mkQuery qid host 1
  let queryBytes := encodeMsg qMsg
  IO.println s!"\n-- query --"
  IO.println s!"question               : {nameStr host} IN A  (id 0x{toHex [0x12,0x34]})"
  IO.println s!"encodeMsg query        : {(queryBytes).length}B  {toHex queryBytes}"

  -- the query wire round-trip, realized on these very bytes
  let qParsed := parseMsg queryBytes
  let qRoundtrips := qParsed == some qMsg
  IO.println s!"parseMsg∘encodeMsg == query (wire round-trip realized) : {qRoundtrips}"

  -- 2. the authoritative resolver ENCODES a response (A 93.184.216.34)
  let rMsg := mkAResponse qid host [[93, 184, 216, 34]]
  let respBytes := encodeMsg rMsg
  IO.println s!"\n-- response (authoritative resolver, encoded) --"
  IO.println s!"encodeMsg response     : {(respBytes).length}B  {toHex respBytes}"

  -- 3. the resolver extracts, over the two byte strings, with the proven logic
  let answers := answersOf queryBytes respBytes
  let ips := resolveA queryBytes respBytes
  IO.println s!"\n-- resolve (Dns.answersOf / resolveA over the wire bytes) --"
  IO.println s!"answersOf returned     : {answers.length} record(s)"
  for a in ips do
    IO.println s!"  resolved A           : {a}  ({dot [(a / 16777216 % 256).toUInt8, (a / 65536 % 256).toUInt8, (a / 256 % 256).toUInt8, (a % 256).toUInt8]})"

  -- 4. the faithfulness cross-check: wire resolve == model decision
  -- `dns_resolve_faithful` PROVES answersOf query resp = answersFor id host A resp;
  -- here we witness it on the concrete bytes (resolved IP lists compared).
  let modelIps := (answersFor qid host 1 respBytes).filterMap (fun
    | .a addr => some addr
    | _ => none)
  let faithful := (ips == modelIps) && !ips.isEmpty
  let expected := ips == [1572395042]
  IO.println s!"\n-- cross-check (realizes dns_resolve_faithful) --"
  IO.println s!"wire resolveA == model answersFor : {ips == modelIps}"
  IO.println s!"resolved list non-empty            : {!ips.isEmpty}"
  IO.println s!"resolved 93.184.216.34 (=1572395042) : {expected}"

  -- 5. negative discipline: a SERVFAIL response with a lying answer resolves to []
  let sfBytes := encodeMsg (mkServfail qid host)
  let sfIps := resolveA queryBytes sfBytes
  IO.println s!"\n-- negative: SERVFAIL (RCODE 2) with a lying answer section --"
  IO.println s!"resolveA on SERVFAIL response      : {sfIps}  (must be [])"
  let sfRefused := sfIps.isEmpty

  -- an ID-mismatched response resolves to []
  let wrongId := encodeMsg (mkAResponse 0xDEAD host [[93, 184, 216, 34]])
  let wrongIps := resolveA queryBytes wrongId
  IO.println s!"resolveA on wrong-ID response      : {wrongIps}  (must be [])"
  let idRefused := wrongIps.isEmpty

  if qRoundtrips && faithful && expected && sfRefused && idRefused then do
    IO.println "\nPASS — query encoded, response encoded, resolver extracted the address;"
    IO.println "       the decode→resolve chain equals the proven model, error/mismatch refused."
    IO.println "FULL RESOLVER EXCHANGE COMPLETE (drorb-native, byte-level, verified codec+extraction)."
    return 0
  else do
    IO.eprintln "\nFAIL — a stage of the resolver pipeline did not cross-check."
    return 1

/-! ## Real interop: DNS-over-TCP to an external resolver (named residual)

RFC 1035 §4.2.2: a DNS message over TCP is prefixed with a 2-octet big-endian
length. This drives the SAME proven `encodeMsg` query and `resolveA` extraction
against a real resolver over `ffi/derp_net.c`. Residual: needs a reachable DNS
server that speaks DNS-over-TCP. -/

def recvTimeout : UInt32 := 10000

def be16enc (n : Nat) : ByteArray := ByteArray.mk #[(n / 256 % 256).toUInt8, (n % 256).toUInt8]
def be16dec (b : ByteArray) : Nat := (b.get! 0).toNat * 256 + (b.get! 1).toNat

def resolve (server : String) (port : UInt16) (host : String) (qtype : Nat) : IO UInt32 := do
  let name := labelsOfHost host
  let qid : Nat := 0x2b2b
  let qMsg := mkQuery qid name qtype
  let queryBytes := encodeMsg qMsg
  IO.println s!"== dns-resolve-live resolve : {host} (qtype {qtype}) via {server}:{port} over TCP =="
  let fd ← tcpConnect server port
  IO.println "connected (real TCP)."
  -- RFC 1035 §4.2.2: 2-octet length prefix + message
  let qba := baOfBytes queryBytes
  tcpSend fd (be16enc qba.size)
  tcpSend fd qba
  IO.println s!"sent encodeMsg query ({qba.size}B)."
  let some lenb ← tcpRecvExact fd 2 recvTimeout
    | do IO.eprintln "no length prefix from resolver"; tcpClose fd; return 1
  let some respba ← tcpRecvExact fd (UInt32.ofNat (be16dec lenb)) recvTimeout
    | do IO.eprintln "short response from resolver"; tcpClose fd; return 1
  tcpClose fd
  let respBytes := bytesOfBa respba
  IO.println s!"received response ({respba.size}B)."
  let ips := resolveA queryBytes respBytes
  let ip6s := resolveAAAA queryBytes respBytes
  IO.println s!"resolveA   : {ips}"
  IO.println s!"resolveAAAA: {ip6s}"
  if ips.isEmpty && ip6s.isEmpty then do
    IO.eprintln "no addresses extracted (mismatch/error/empty — see model soundness)"; return 1
  else do
    for a in ips do
      IO.println s!"  A    {dot [(a / 16777216 % 256).toUInt8, (a / 65536 % 256).toUInt8, (a / 256 % 256).toUInt8, (a % 256).toUInt8]}"
    IO.println "DONE — real resolver reply decoded by the proven resolver."
    return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["selftest"] => selftest
  | ["resolve", server, portS, host] =>
    match portS.toNat? with
    | some p => resolve server p.toUInt16 host 1
    | none => do IO.eprintln "resolve <server> <port> <name> [qtype]: bad port"; return 1
  | ["resolve", server, portS, host, qtS] =>
    match portS.toNat?, qtS.toNat? with
    | some p, some qt => resolve server p.toUInt16 host qt
    | _, _ => do IO.eprintln "resolve <server> <port> <name> [qtype]: bad port/qtype"; return 1
  | _ => do
    IO.eprintln "usage: dns-resolve-live selftest | resolve <server> <port> <name> [qtype]"
    return 1

end DnsResolveLive

def main (args : List String) : IO UInt32 := DnsResolveLive.main args
