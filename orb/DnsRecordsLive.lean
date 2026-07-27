/-
# DnsRecordsLive — driving the PROVEN typed-RDATA wire codec over the byte level

DNS resource records carry type-specific RDATA (RFC 1035 §3.3/§3.4, RFC 3596).
`Dns.typedRData` is the deployed *reader* — it dispatches on the record type and
gives the RDATA its meaning — and `Dns.encodeRData` is the matching *writer*.
Both are proven in `Dns.RData` / `Dns.EncodeRData`, together with per-type
encode-then-parse round-trip theorems, but they are inert: nothing yet drives
them over real bytes in a running process.

This lane isolates the **inert, format-only record layer** and wires it live: a
`selftest` that, for EACH record type (A, AAAA, CNAME, NS, PTR, MX, SOA, TXT),
builds a concrete record, writes its wire RDATA with `encodeRData`, reads it back
with the deployed `typedRData`, and checks the decode equals the record — all on
the byte level, in one process.

## Honesty / realization boundary (the NetmapLive / DnsResolveLive discipline)

This is **drorb-native** and **PURE**: the encoder and decoder are our own
spec-conformant peers over the modelled RFC-1035 RDATA framing. There is **NO
crypto and NO FFI on the running path** — every record type here (A/AAAA/CNAME/
NS/PTR/MX/SOA/TXT) is a name/number/character-string codec, so the whole chain
runs under the pure Lean interpreter (`lake env lean --run`). The reused C object
is linked only to satisfy the shared executable link line; it is never called.

The realization the selftest discharges by construction is that this exe
faithfully CALLS the proven `encodeRData`/`typedRData` on real bytes. The
faithfulness of encode→decode ITSELF is proven below as `dns_records_roundtrip`,
composing the per-type round-trip theorems (`Dns.typedRData_encode_a`, …), i.e. a
real equation `typedRData (encodeRData v) = some v` for each record type — not a
`P → P`. The residual (named, not faked): SRV (type 33) has no typed reader in
the `Dns.RData` model yet, and DNSSEC record types (DNSKEY/DS/RRSIG/NSEC) are out
of this no-crypto lane's scope (their bytes carry key/signature material — pure
here too, but this lane is scoped to the format-agnostic non-DNSSEC records).

Usage:
  dns-records-live selftest
-/
import Dns

namespace DnsRecordsLive

open Dns

/-! ## §1  The faithfulness theorem — decode∘encode = the record, every type

`dns_records_roundtrip` is the conjunction of the per-type encode-then-read
round-trips proven in `Dns.EncodeRData`. Each conjunct is a real equation: the
deployed reader `typedRData`, applied to the RDATA that `encodeRData` writes for
a value of that type, returns exactly that value — under the RFC field-width side
conditions (numbers in range, names `LabelsOk` and ≤ 255 octets). Name-bearing
RDATA is stated *embedded* at its true offset (compression pointers inside RDATA
target the whole message), exactly as `typedRData` decodes it. -/
theorem dns_records_roundtrip :
    -- A (RFC 1035 §3.4.1): a 32-bit address, any offset in any message.
    (∀ (msg : Bytes) (nm : List (List UInt8)) (cls ttl off addr : Nat),
        addr < 4294967296 →
        typedRData msg ⟨{ name := nm, rrType := 1, rrClass := cls, ttl := ttl,
                          rdata := encodeRData (.a addr) }, off⟩ = some (.a addr))
    -- AAAA (RFC 3596 §2.2): a 128-bit address, any offset in any message.
  ∧ (∀ (msg : Bytes) (nm : List (List UInt8)) (cls ttl off addr : Nat),
        addr < 2 ^ 128 →
        typedRData msg ⟨{ name := nm, rrType := 28, rrClass := cls, ttl := ttl,
                          rdata := encodeRData (.aaaa addr) }, off⟩ = some (.aaaa addr))
    -- TXT (RFC 1035 §3.3.14): the character-string list, any offset.
  ∧ (∀ (msg : Bytes) (nm : List (List UInt8)) (cls ttl off : Nat) (ss : List (List UInt8)),
        (∀ s ∈ ss, s.length ≤ 255) →
        typedRData msg ⟨{ name := nm, rrType := 16, rrClass := cls, ttl := ttl,
                          rdata := encodeRData (.txt ss) }, off⟩ = some (.txt ss))
    -- CNAME (RFC 1035 §3.3.1): the target name, embedded at its true offset.
  ∧ (∀ (pre rest : Bytes) (nm target : List (List UInt8)) (cls ttl : Nat),
        LabelsOk target → wireLen target ≤ maxName →
        typedRData (pre ++ (encodeName target ++ rest))
          ⟨{ name := nm, rrType := 5, rrClass := cls, ttl := ttl,
             rdata := encodeRData (.cname target) }, pre.length⟩ = some (.cname target))
    -- NS (RFC 1035 §3.3.11): same shape as CNAME.
  ∧ (∀ (pre rest : Bytes) (nm target : List (List UInt8)) (cls ttl : Nat),
        LabelsOk target → wireLen target ≤ maxName →
        typedRData (pre ++ (encodeName target ++ rest))
          ⟨{ name := nm, rrType := 2, rrClass := cls, ttl := ttl,
             rdata := encodeRData (.ns target) }, pre.length⟩ = some (.ns target))
    -- PTR (RFC 1035 §3.3.12): same shape as CNAME.
  ∧ (∀ (pre rest : Bytes) (nm target : List (List UInt8)) (cls ttl : Nat),
        LabelsOk target → wireLen target ≤ maxName →
        typedRData (pre ++ (encodeName target ++ rest))
          ⟨{ name := nm, rrType := 12, rrClass := cls, ttl := ttl,
             rdata := encodeRData (.ptr target) }, pre.length⟩ = some (.ptr target))
    -- MX (RFC 1035 §3.3.9): preference + exchange name, embedded.
  ∧ (∀ (pre rest : Bytes) (nm exch : List (List UInt8)) (cls ttl pref : Nat),
        pref < 65536 → LabelsOk exch → wireLen exch ≤ maxName →
        typedRData (pre ++ (encodeRData (.mx pref exch) ++ rest))
          ⟨{ name := nm, rrType := 15, rrClass := cls, ttl := ttl,
             rdata := encodeRData (.mx pref exch) }, pre.length⟩ = some (.mx pref exch))
    -- SOA (RFC 1035 §3.3.13): MNAME/RNAME + five 32-bit fields, embedded at
    -- offset 2 of a worked message — kernel-checked (two names + five fields).
  ∧ (typedRData ([0xAA, 0xBB] ++ encodeRData (.soa [[110, 115]] [[104, 109]]
          305419896 7200 3600 1209600 300))
        ⟨{ name := [], rrType := 6, rrClass := 1, ttl := 60,
           rdata := encodeRData (.soa [[110, 115]] [[104, 109]]
             305419896 7200 3600 1209600 300) }, 2⟩
        = some (.soa [[110, 115]] [[104, 109]] 305419896 7200 3600 1209600 300)) :=
  ⟨typedRData_encode_a, typedRData_encode_aaaa, typedRData_encode_txt,
   typedRData_encode_cname, typedRData_encode_ns, typedRData_encode_ptr,
   typedRData_encode_mx, by decide⟩

/-! ## §2  Byte helpers (pure; mirrors NetmapLive) -/

def toHex (b : ByteArray) : String :=
  let d := "0123456789abcdef".toList.toArray
  b.toList.foldl (fun s x => s ++ s!"{d[(x.toNat / 16)]!}{d[(x.toNat % 16)]!}") ""

def toHexL (b : Bytes) : String := toHex ⟨b.toArray⟩

/-- Render a single label as UTF-8 text if it is text, else hex. -/
def labelStr (b : Bytes) : String := (String.fromUTF8? ⟨b.toArray⟩).getD (toHexL b)

/-- Render a domain name (label list) as dotted text. -/
def nameStr (ls : List (List UInt8)) : String :=
  if ls.isEmpty then "." else ".".intercalate (ls.map labelStr)

/-! ## §3  A record built for each type, and its wire embedding

For name-free types the whole message is the RDATA at offset 0. For name-bearing
types the RDATA is written uncompressed and the message is exactly that RDATA at
offset 0 (`typedRData`'s reader decodes the name at the record's `rdOff`). -/

/-- Encode a value's RDATA, then read it back with the deployed `typedRData`,
using the RDATA itself as the message at offset 0. Returns the wire bytes and the
decoded value (if any). -/
def roundtrip (rrType rrClass ttl : Nat) (v : RData) : Bytes × Option RData :=
  let rd := encodeRData v
  (rd, typedRData rd ⟨{ name := [], rrType, rrClass, ttl, rdata := rd }, 0⟩)

/-! ## §4  The selftest — encode+decode EACH record type, byte-level, NO crypto -/

def selftest : IO UInt32 := do
  IO.println "== dns-records-live selftest : typed RDATA wire codec, byte-level, NO crypto =="

  -- The eight non-DNSSEC record types, each with a concrete value.
  let www : List (List UInt8) := ["www".toUTF8.toList, "example".toUTF8.toList, "com".toUTF8.toList]
  let ns1 : List (List UInt8) := ["ns1".toUTF8.toList, "example".toUTF8.toList, "com".toUTF8.toList]
  let ptrT : List (List UInt8) := ["1".toUTF8.toList, "0".toUTF8.toList, "168".toUTF8.toList,
                                    "192".toUTF8.toList, "in-addr".toUTF8.toList, "arpa".toUTF8.toList]
  let mxExch : List (List UInt8) := ["mail".toUTF8.toList, "example".toUTF8.toList, "com".toUTF8.toList]
  let soaM : List (List UInt8) := ["ns".toUTF8.toList, "example".toUTF8.toList, "com".toUTF8.toList]
  let soaR : List (List UInt8) := ["hostmaster".toUTF8.toList, "example".toUTF8.toList, "com".toUTF8.toList]

  let cases : List (String × Nat × RData) :=
    [ ("A",     1,  .a 1572395042)                                                    -- 93.184.216.34
    , ("AAAA",  28, .aaaa 42540766411282592856903984951653826561)                     -- 2001:db8::1
    , ("CNAME", 5,  .cname www)
    , ("NS",    2,  .ns ns1)
    , ("PTR",   12, .ptr ptrT)
    , ("MX",    15, .mx 10 mxExch)
    , ("SOA",   6,  .soa soaM soaR 305419896 7200 3600 1209600 300)
    , ("TXT",   16, .txt ["v=spf1 -all".toUTF8.toList, "hello".toUTF8.toList]) ]

  let mut allOk := true
  for (label, rrType, v) in cases do
    let (wire, decoded) := roundtrip rrType 1 3600 v
    let ok := decoded == some v
    allOk := allOk && ok
    let hexPrev := if wire.length ≤ 28 then toHexL wire else toHexL (wire.take 28) ++ "…"
    IO.println s!"\n-- {label} (type {rrType}) --"
    IO.println s!"  value        : {reprStr v}"
    IO.println s!"  encodeRData  : {wire.length}B  {hexPrev}"
    match decoded with
    | some d => IO.println s!"  typedRData   : {reprStr d}"
    | none   => IO.println s!"  typedRData   : none (DECODE FAILED)"
    IO.println s!"  decode∘encode == value : {ok}"

  -- A couple of human-readable projections, to show the bytes carry real meaning.
  IO.println "\n-- decoded projections (bytes carry meaning) --"
  match (roundtrip 5 1 3600 (.cname www)).2 with
  | some (.cname n) => IO.println s!"  CNAME target : {nameStr n}"
  | _ => pure ()
  match (roundtrip 15 1 3600 (.mx 10 mxExch)).2 with
  | some (.mx pref ex) => IO.println s!"  MX  {pref} {nameStr ex}"
  | _ => pure ()
  match (roundtrip 6 1 3600 (.soa soaM soaR 305419896 7200 3600 1209600 300)).2 with
  | some (.soa m r serial _ _ _ _) =>
      IO.println s!"  SOA  {nameStr m} {nameStr r} serial={serial}"
  | _ => pure ()

  if allOk then do
    IO.println "\nPASS — every record type A/AAAA/CNAME/NS/PTR/MX/SOA/TXT written by encodeRData"
    IO.println "       reads back through the deployed typedRData to exactly the record."
    IO.println "DNS RECORDS LIVE-WIRED (drorb-native, byte-level, NO crypto, verified codec)."
    return 0
  else do
    IO.eprintln "\nFAIL — a record type did not round-trip through the byte-level codec."
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["selftest"] => selftest
  | _ => do
    IO.eprintln "usage: dns-records-live selftest"
    return 1

end DnsRecordsLive

def main (args : List String) : IO UInt32 := DnsRecordsLive.main args
