import Dns

/-!
# DNS conformance check driver

Feeds captured real DNS wire messages (query/response pairs, hex-encoded in a
manifest file) through the deployed `Dns` functions — `Dns.parseMsg`,
`Dns.typedRData`, `Dns.answersOf`, `Dns.Msg.extendedRcode`,
`Dns.wantsTcpRetryOf`, `Dns.unframeTcp`, the typed SvcParam/cookie readers and
the NSEC/NSEC3 bitmap decoder — and prints a line-oriented report per capture.
A companion script compares the report against dig's decoded view of the same
exchanges.

A manifest line may carry a fourth token `tcp`, marking the pair as raw TCP
stream octets (RFC 1035 §4.2.2 length-prefixed); those are unframed with
`Dns.unframeTcp` first and the outcome reported on a `FRAME` line.

Run from the package root:

    lake env lean --run conformance/dns/DnsCheck.lean conformance/dns/captures/manifest.txt
-/

open Dns

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def hexBytes : List Char → Option (List UInt8)
  | [] => some []
  | h :: l :: rest => do
    let hv ← hexDigit h
    let lv ← hexDigit l
    let tail ← hexBytes rest
    pure (UInt8.ofNat (hv * 16 + lv) :: tail)
  | _ => none

def labelStr (l : List UInt8) : String :=
  String.mk (l.map fun b => Char.ofNat b.toNat)

def nameStr (n : List (List UInt8)) : String :=
  if n.isEmpty then "." else String.intercalate "." (n.map labelStr)

def ip4Str (a : Nat) : String :=
  s!"{a / 16777216 % 256}.{a / 65536 % 256}.{a / 256 % 256}.{a % 256}"

def hexPad (n w : Nat) : String :=
  let s := String.mk (Nat.toDigits 16 n)
  (if s.length < w then String.mk (List.replicate (w - s.length) '0') else "") ++ s

def bytesHex (l : List UInt8) : String :=
  if l.isEmpty then "-" else String.join (l.map fun b => hexPad b.toNat 2)

/-- Decoded type-bitmap numbers, space-separated ("badbitmap" on a walk
failure). -/
def bitmapStr (bm : List UInt8) : String :=
  match bitmapTypes bm with
  | none => "badbitmap"
  | some ts => String.intercalate "," (ts.map toString)

/-- Typed SvcParams summary for SVCB/HTTPS records. -/
def svcParamsStr (ps : List (Nat × List UInt8)) : String :=
  let alpn := match svcAlpn ps with
    | some ids => s!" alpn={String.intercalate "," (ids.map labelStr)}"
    | none => ""
  let port := match svcPort ps with
    | some p => s!" port={p}"
    | none => ""
  let v4 := match svcIpv4Hint ps with
    | some as => s!" ipv4hint={String.intercalate "," (as.map ip4Str)}"
    | none => ""
  s!"{ps.length}{alpn}{port}{v4}"

/-- Typed EDNS option summary (cookies). -/
def optionsStr (os : List (Nat × List UInt8)) : String :=
  match ednsCookie os with
  | some (c, s) => s!"{os.length} cookie={bytesHex c}/{bytesHex s}"
  | none => s!"{os.length}"

def rdataStr : RData → String
  | .a addr => s!"A {ip4Str addr}"
  | .aaaa addr => s!"AAAA {hexPad addr 32}"
  | .cname n => s!"CNAME {nameStr n}"
  | .ns n => s!"NS {nameStr n}"
  | .ptr n => s!"PTR {nameStr n}"
  | .mx p e => s!"MX {p} {nameStr e}"
  | .soa m r serial refresh retry expire minimum =>
    s!"SOA {nameStr m} {nameStr r} {serial} {refresh} {retry} {expire} {minimum}"
  | .txt ss => s!"TXT {ss.length} {String.join (ss.map labelStr)}"
  | .dnskey f p a k =>
    s!"DNSKEY {f} {p} {a} {k.length} tag={keyTag (encodeRData (.dnskey f p a k))}"
  | .rrsig tc alg lab ttl exp inc tag signer sig =>
    s!"RRSIG {tc} {alg} {lab} {ttl} {exp} {inc} {tag} {nameStr signer} {sig.length}"
  | .ds tag alg dt d => s!"DS {tag} {alg} {dt} {d.length}"
  | .nsec nxt bm => s!"NSEC {nameStr nxt} {bitmapStr bm}"
  | .nsec3 alg fl iter salt next bm =>
    s!"NSEC3 {alg} {fl} {iter} {bytesHex salt} {bytesHex next} {bitmapStr bm}"
  | .nsec3param alg fl iter salt => s!"NSEC3PARAM {alg} {fl} {iter} {bytesHex salt}"
  | .svcb pr t ps => s!"SVCB {pr} {nameStr t} {svcParamsStr ps}"
  | .opt u er v dob os => s!"OPT {u} {er} {v} {dob} {optionsStr os}"
  | .other rd => s!"OTHER {rd.length}"

/-- The typed cookie of a message's OPT record, if any. -/
def msgCookie (msg : Bytes) (m : Msg) : Option (List UInt8 × List UInt8) :=
  match m.ednsOpt with
  | none => none
  | some r =>
    match typedRData msg r with
    | some (.opt _ _ _ _ os) => ednsCookie os
    | _ => none

def report (name : String) (q r : Bytes) (frame : Option Bool) : IO Unit := do
  IO.println s!"CAPTURE {name}"
  match frame with
  | none => pure ()
  | some b => IO.println s!"FRAME {if b then "ok" else "fail"}"
  match parseMsg q with
  | none => IO.println "QPARSE fail"
  | some qm => do
    IO.println "QPARSE ok"
    match msgCookie q qm with
    | none => pure ()
    | some (c, s) => IO.println s!"QCOOKIE {bytesHex c} {bytesHex s}"
  match parseMsg r with
  | none => IO.println "RPARSE fail"
  | some m => do
    IO.println "RPARSE ok"
    IO.println s!"RCODE {m.header.rcode}"
    IO.println s!"XRCODE {m.extendedRcode}"
    IO.println s!"TC {m.header.tc}"
    IO.println s!"RETRY {wantsTcpRetryOf q r}"
    IO.println s!"COUNTS {m.header.qdCount} {m.header.anCount} {m.header.nsCount} {m.header.arCount}"
    for q in m.questions do
      IO.println s!"Q {nameStr q.qname} {q.qtype} {q.qclass}"
    for (sec, rs) in [("answer", m.answers), ("authority", m.authority),
                      ("additional", m.additional)] do
      for rr in rs do
        match typedRData r rr with
        | none => IO.println s!"RR {sec} {rr.rr.rrType} {nameStr rr.rr.name} MALFORMED"
        | some d => IO.println s!"RR {sec} {rr.rr.rrType} {nameStr rr.rr.name} {rdataStr d}"
  for d in answersOf q r do
    IO.println s!"ANS {rdataStr d}"
  IO.println "END"

def main (args : List String) : IO Unit := do
  let path := args.getD 0 "conformance/dns/captures/manifest.txt"
  let txt ← IO.FS.readFile path
  for line in txt.splitOn "\n" do
    let line := line.trim
    if line.isEmpty then
      continue
    match line.splitOn " " with
    | [name, qh, rh] =>
      match hexBytes qh.toList, hexBytes rh.toList with
      | some q, some r => report name q r none
      | _, _ => do
        IO.println s!"CAPTURE {name}"
        IO.println "HEXERR"
        IO.println "END"
    | [name, qh, rh, "tcp"] =>
      match hexBytes qh.toList, hexBytes rh.toList with
      | some qs, some rs =>
        -- RFC 1035 §4.2.2: both directions carry the two-octet length prefix.
        match unframeTcp qs, unframeTcp rs with
        | some (qm, qrest), some (rm, rrest) =>
          report name qm rm (some (qrest.isEmpty && rrest.isEmpty))
        | _, _ => do
          IO.println s!"CAPTURE {name}"
          IO.println "FRAME fail"
          IO.println "QPARSE fail"
          IO.println "RPARSE fail"
          IO.println "END"
      | _, _ => do
        IO.println s!"CAPTURE {name}"
        IO.println "HEXERR"
        IO.println "END"
    | _ => pure ()
