/-
# SvcbLive — driving the PROVEN SVCB/HTTPS RDATA codec over the byte level

SVCB (type 64) and HTTPS (type 65) resource records (RFC 9460 §2.2) share one
wire shape:

```
  SvcPriority(16)  TargetName(domain name)  SvcParams(key(16) len(16) value list)
```

`Dns.typedRData` is the deployed *reader* for both type codes; `Dns.encodeRData`
is the matching *writer*; and `Dns.svcb_encode_decode` proves the composed record
round-trips (priority, target name, and the SvcParams TLV list written by
`encodeRData` parse back verbatim through `typedRData`, embedded at any offset).
`Dns.keysAscending` / `Dns.svcparams_sorted` capture the §2.2 rule that SvcParams
appear in strictly increasing key order, and that this order survives the wire.
All of that is proven but inert: nothing yet drives it over real bytes in a
running process.

This lane wires it live: a `selftest` that builds a concrete HTTPS record
(SvcPriority + TargetName + the four SvcParams an HTTPS record carries in
practice — `alpn`(1), `port`(3), `ipv4hint`(4), `ipv6hint`(6), keys strictly
ascending), writes its wire RDATA with `encodeRData`, reads it back with the
deployed `typedRData`, and checks the decode equals the record and that the
decoded SvcParams are still ascending — all on the byte level, one process.

## Honesty / realization boundary (the NetmapLive / DnsRecordsLive discipline)

This is **drorb-native** and **PURE**: the encoder and decoder are our own
spec-conformant peers over the modelled RFC-9460 RDATA framing. There is **NO
crypto and NO FFI on the running path** — SvcPriority is a 16-bit number, the
TargetName is an RFC-1035 name codec, and each SvcParam is a `key/len/value` TLV,
so the whole chain runs under the pure Lean interpreter (`lake env lean --run`).
This is a **rung-2 selftest** (a drorb-native encode/decode against our own
modelled wire), NOT the deployed serve and NOT byte-exact interop with a live
authoritative server (which additionally needs the message frame + real
resolver transport — the named residual).

The realization this exe discharges by construction is that it faithfully CALLS
the proven `encodeRData`/`typedRData` on real bytes. The faithfulness of
encode→decode ITSELF is proven below as `svcb_roundtrip`: for any priority,
target and SvcParams meeting the RFC field widths and in strictly increasing key
order, `typedRData (encodeRData (.svcb priority target params)) = some (.svcb
priority target params)` AND the decoded params are still ascending — a real
equation (composed from `Dns.svcb_encode_decode`), not a `P → P`, and inhabited
by the concrete HTTPS record `https_record_roundtrips_live` the selftest drives.

Usage:
  svcb-live selftest
-/
import Dns.Svcb

namespace SvcbLive

open Dns

/-! ## §1  The faithfulness theorem — decode∘encode = the record, order preserved

`svcb_roundtrip` composes `Dns.svcb_encode_decode` (the embedded round-trip proven
in `Dns.Svcb`) at the concrete offset the selftest uses (the RDATA is the whole
message at offset 0, so the target name, decoded against the message at `rdOff+2`,
resolves at its true position). The conclusion carries `keysAscending params` too:
an HTTPS record whose SvcParams are in strictly increasing key order (RFC 9460
§2.2) decodes off the wire to a params list that is *still* ascending. The
hypotheses are the exact RFC side conditions (priority 16-bit, target a legal
name ≤ 255 octets, each SvcParam key and value length 16-bit) plus §2.2 ordering
— real premises, discharged concretely below, so nothing is vacuous. -/
theorem svcb_roundtrip (target : List (List UInt8)) (priority : Nat)
    (params : List (Nat × List UInt8))
    (hpri : priority < 65536) (hok : LabelsOk target) (hcap : wireLen target ≤ maxName)
    (hparams : ∀ p ∈ params, p.1 < 65536 ∧ p.2.length < 65536)
    (hsorted : keysAscending params) :
    typedRData (encodeRData (.svcb priority target params))
        ⟨{ name := [], rrType := 65, rrClass := 1, ttl := 3600,
           rdata := encodeRData (.svcb priority target params) }, 0⟩
      = some (.svcb priority target params)
    ∧ keysAscending params := by
  refine ⟨?_, hsorted⟩
  have h := Dns.svcb_encode_decode [] [] [] target 1 3600 priority params hpri hok hcap hparams
  simpa using h

/-! ## §2  The concrete HTTPS record (non-vacuity witness)

`cdn.example.com` HTTPS RR, priority 1, four SvcParams in ascending key order:
`alpn` (h3, h2), `port` 443, `ipv4hint` 104.16.132.229, `ipv6hint`
2606:4700::6810:84e5. The target name reuses `Dns.httpsTarget` (= cdn.example.com)
and its proven `LabelsOk` witness. -/

/-- The SvcParams of a real HTTPS record, keys strictly ascending (1 < 3 < 4 < 6):
alpn, port, ipv4hint, ipv6hint. -/
def liveParams : List (Nat × List UInt8) :=
  [ (1, [2, 104, 51, 2, 104, 50]),        -- alpn: "h3", "h2"
    (3, [0x01, 0xBB]),                      -- port 443
    (4, [104, 16, 132, 229]),               -- ipv4hint 104.16.132.229
    (6, [0x26, 0x06, 0x47, 0x00, 0, 0, 0, 0, 0, 0, 0, 0, 0x68, 0x10, 0x84, 0xE5]) ] -- ipv6hint

/-- `liveParams` is in strictly increasing key order — `keysAscending` is not
vacuously satisfiable here. -/
theorem liveParams_ascending : keysAscending liveParams :=
  ⟨by decide, by decide, by decide, trivial⟩

/-- **Non-vacuity witness.** The concrete `cdn.example.com` HTTPS record with the
alpn/port/ipv4hint/ipv6hint SvcParams round-trips through the deployed reader and
its decoded SvcParams are still ascending — a live instance of `svcb_roundtrip`
with every side condition discharged, so that theorem is inhabited. -/
theorem https_record_roundtrips_live :
    typedRData (encodeRData (.svcb 1 httpsTarget liveParams))
        ⟨{ name := [], rrType := 65, rrClass := 1, ttl := 3600,
           rdata := encodeRData (.svcb 1 httpsTarget liveParams) }, 0⟩
      = some (.svcb 1 httpsTarget liveParams)
    ∧ keysAscending liveParams :=
  svcb_roundtrip httpsTarget 1 liveParams (by decide) httpsTarget_ok (by decide)
    (by decide) liveParams_ascending

/-! ## §3  Byte helpers (pure; mirrors NetmapLive / DnsRecordsLive) -/

def toHex (b : ByteArray) : String :=
  let d := "0123456789abcdef".toList.toArray
  b.toList.foldl (fun s x => s ++ s!"{d[(x.toNat / 16)]!}{d[(x.toNat % 16)]!}") ""

def toHexL (b : Bytes) : String := toHex ⟨b.toArray⟩

/-- Render a single label as UTF-8 text if it is text, else hex. -/
def labelStr (b : Bytes) : String := (String.fromUTF8? ⟨b.toArray⟩).getD (toHexL b)

/-- Render a domain name (label list) as dotted text. -/
def nameStr (ls : List (List UInt8)) : String :=
  if ls.isEmpty then "." else ".".intercalate (ls.map labelStr)

/-- Human name for a registered SvcParamKey (RFC 9460 §14.3.2). -/
def svcKeyName (k : Nat) : String :=
  match k with
  | 0 => "mandatory" | 1 => "alpn" | 2 => "no-default-alpn" | 3 => "port"
  | 4 => "ipv4hint" | 5 => "ech" | 6 => "ipv6hint" | _ => s!"key{k}"

/-- Decode an `alpn` (key 1) value — a sequence of length-prefixed protocol ids —
into its protocol strings. -/
partial def alpnIds (v : Bytes) : List String :=
  match v with
  | [] => []
  | n :: rest =>
    let id := rest.take n.toNat
    labelStr id :: alpnIds (rest.drop n.toNat)

/-- Render one SvcParam value in its key-specific human form. -/
def svcValue (k : Nat) (v : Bytes) : String :=
  match k with
  | 1 => s!"[{", ".intercalate (alpnIds v)}]"                    -- alpn
  | 3 => s!"{Dns.be16At v 0}"                                     -- port
  | 4 => ".".intercalate (v.map (fun b => s!"{b.toNat}"))        -- ipv4hint (dotted)
  | _ => toHexL v                                                 -- ipv6hint etc. (hex)

/-! ## §4  The selftest — encode+decode an SVCB/HTTPS RR, byte-level, NO crypto -/

def selftest : IO UInt32 := do
  IO.println "== svcb-live selftest : SVCB/HTTPS RDATA wire codec, byte-level, NO crypto =="

  -- ── the concrete HTTPS record: cdn.example.com, priority 1, four SvcParams ──
  let priority := 1
  let target := httpsTarget                    -- cdn.example.com
  let params := liveParams                     -- alpn / port / ipv4hint / ipv6hint
  let rec0 : RData := .svcb priority target params

  IO.println s!"\n-- record to encode --"
  IO.println s!"SvcPriority            : {priority}"
  IO.println s!"TargetName             : {nameStr target}"
  IO.println s!"SvcParams (key order)  : {params.map (fun p => svcKeyName p.1)}"

  -- ── ENCODE the RDATA, then DECODE it back through the deployed typedRData ──
  let wire := encodeRData rec0
  IO.println s!"\n-- encodeRData (wire RDATA) --"
  IO.println s!"wire bytes             : {wire.length}B  {toHexL (wire.take 28)}…"

  -- the RDATA is the whole message at offset 0; typedRData decodes the target
  -- name against the message at rdOff+2, so it resolves at its true position.
  let httpsAt : RRAt := ⟨{ name := [], rrType := 65, rrClass := 1, ttl := 3600, rdata := wire }, 0⟩
  let svcbAt  : RRAt := ⟨{ name := [], rrType := 64, rrClass := 1, ttl := 3600, rdata := wire }, 0⟩
  let some decoded := typedRData wire httpsAt
    | do IO.eprintln "typedRData FAILED to decode the HTTPS RR"; return 1

  let ok := decoded == rec0
  IO.println s!"\n-- typedRData (deployed reader, type 65 HTTPS) --"
  IO.println s!"decode∘encode == record : {ok}"

  -- ── project the decoded fields, to show the bytes carry real meaning ──
  match decoded with
  | .svcb pri tgt ps =>
    IO.println s!"  SvcPriority          : {pri}"
    IO.println s!"  TargetName           : {nameStr tgt}"
    for p in ps do
      IO.println s!"  SvcParam {svcKeyName p.1} (key {p.1}) = {svcValue p.1 p.2}"
  | _ => IO.eprintln "  decoded to a non-SVCB RData (unexpected)"

  -- ── §2.2 key order survives the wire ──
  let decParams := match decoded with | .svcb _ _ ps => ps | _ => []
  let sortedOnWire := (decParams.map (·.1)) == [1, 3, 4, 6]
      && (decParams == params)
  IO.println s!"\n-- RFC 9460 §2.2 key order --"
  IO.println s!"decoded SvcParam keys    : {decParams.map (·.1)}"
  IO.println s!"strictly ascending (1<3<4<6) & verbatim : {sortedOnWire}"

  -- ── HTTPS (type 65) decodes identically to SVCB (type 64): same wire format ──
  let httpsIsSvcb := typedRData wire httpsAt == typedRData wire svcbAt
  IO.println s!"\n-- HTTPS is SVCB (RFC 9460 §9) --"
  IO.println s!"typedRData@65 == typedRData@64 : {httpsIsSvcb}"

  if ok && sortedOnWire && httpsIsSvcb then do
    IO.println "\nPASS — the SVCB/HTTPS record (SvcPriority + TargetName + alpn/port/ipv4hint/ipv6hint)"
    IO.println "       written by encodeRData reads back through the deployed typedRData to exactly"
    IO.println "       the record, SvcParams still in strictly increasing key order (RFC 9460 §2.2)."
    IO.println "SVCB/HTTPS LIVE-WIRED (drorb-native rung-2 selftest, byte-level, NO crypto, verified codec)."
    return 0
  else do
    IO.eprintln "\nFAIL — the SVCB/HTTPS record did not round-trip through the byte-level codec."
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["selftest"] => selftest
  | _ => do
    IO.eprintln "usage: svcb-live selftest"
    return 1

end SvcbLive

def main (args : List String) : IO UInt32 := SvcbLive.main args
