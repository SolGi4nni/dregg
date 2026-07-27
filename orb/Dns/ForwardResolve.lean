import Dns

/-!
# Forward resolution (A / AAAA), end to end — encode → wire → resolve

The extraction layer of `Dns.Resolve` (`answersOf` / `resolveA` / `resolveAAAA`)
decides what a response *answers* to the query a resolver sent: RFC 1035 §7.3
response matching (ID, QR, opcode, TC, the RFC 6891 §6.1.3 extended RCODE), the
§3.3.1 CNAME chase, and the whole-section scan. This module drives that layer
**forward, end to end** against the proven encoders (`Dns.encodeMsg`): an
authoritative peer that holds a small **zone** encodes a positive answer, and
the client's `resolveA` / `resolveAAAA` extract *exactly the zone's record* back
out of the emitted wire bytes — the encoder and the extractor are pinned to each
other on real bytes, not just asserted separately.

The three obligations of forward resolution, each an equation the REAL
encode-then-parse-then-extract pipeline reduces to (`decide`, no `native_decide`):

* **`forward_resolve_a`** — an `A` query (RFC 1035 §3.4.1) for a name the zone
  holds resolves to that name's proven `A` address, extracted from the bytes the
  authoritative peer's `encodeMsg` emitted.
* **`forward_resolve_aaaa`** — an `AAAA` query (RFC 3596 §2.2) for the same name
  resolves to that name's proven 128-bit `AAAA` address.
* **`resolve_nxdomain`** — a query for a name the zone does **not** hold, against
  the authoritative peer's NXDOMAIN response (RFC 1035 §4.1.1, RCODE 3), resolves
  to `[]` — not a wrong answer, not a leaked address from another name.

and the general guarantee behind them:

* **`forward_resolve_sound`** — *no fabricated answers.* Any `A` address that
  forward resolution extracts is backed by a real answer record of type 1, class
  IN, in a non-error response — never invented. (The `AAAA` twin,
  `forward_resolve_aaaa_sound`, is the same for type 28.) These are corollaries
  of `Dns.answersFor_sound`, with the membership of the extracted address as the
  real hypothesis (not `P → P`).

## Realization boundary (the DnsResolveLive discipline)

This is **drorb-native** and **PURE**: the authoritative peer and the client
resolver are our own spec-conformant peers over the modelled RFC 1035 wire
format, driven byte-to-byte through `encodeMsg` → `parseMsg` → `resolveA` in one
process. There is **NO crypto and NO FFI** on the running path — A/AAAA
resolution is pure name/number codec — so the `selftest` runs under the Lean
interpreter (`lake env lean --run`). The gap the selftest discharges by
construction is only that the exe faithfully CALLS the proven functions on real
bytes; the faithfulness of encode→resolve ITSELF is the `decide` equations here.

**Deployment note (a real residual, not papered over).** Forward resolution is
NOT exposed as a network endpoint by the deployed Rust dataplane: `serve.rs`
routes HTTP/HTTPS/L4/QUIC/admin only — there is no DNS/UDP-53 server and no
DoH `/dns-query` route to `curl`/`dig`. The deployed *use* of this code is the
reactor's upstream-connect path (`Reactor.DnsWire.resolve`, which reads the
first `A` answer before a proxy dial) plus the `*Live` selftests that run the
extraction in-process. The runnable realization exercised here is the in-process
byte-driven `selftest`, not a socket resolver.
-/

namespace Dns.ForwardResolve

open Dns

/-! ## The zone

A minimal authoritative zone: one owner name (`www.example.com`) with a proven
`A` and `AAAA` record. `93.184.216.34` (RFC 5737 documentation range's sibling,
the classic example.com address) and `2606:4700:10::ac42:93f3`. -/

/-- The zone's owner name, uncompressed labels (RFC 1035 §3.1). -/
def wwwExample : List (List UInt8) :=
  [[119, 119, 119], [101, 120, 97, 109, 112, 108, 101], [99, 111, 109]]

/-- A name the zone does NOT hold (`dn.example.com`). -/
def dnExample : List (List UInt8) :=
  [[100, 110], [101, 120, 97, 109, 112, 108, 101], [99, 111, 109]]

/-- The zone's `A` address, 4 octets big-endian = `93.184.216.34`. -/
def zoneA_bytes : List UInt8 := [93, 184, 216, 34]

/-- `93.184.216.34` as the 32-bit number `Dns.be32` reads. -/
def zoneA_num : Nat := 1572395042

/-- The zone's `AAAA` address, 16 octets = `2606:4700:10::ac42:93f3`. -/
def zoneAAAA_bytes : List UInt8 :=
  [0x26, 0x06, 0x47, 0x00, 0x00, 0x10, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0xAC, 0x42, 0x93, 0xF3]

/-- `2606:4700:10::ac42:93f3` as the 128-bit number the AAAA reader produces. -/
def zoneAAAA_num : Nat := 50543257672079214217829785593155064819

/-! ## The query the stub resolver sends -/

/-- An `A` query for `www.example.com`, id 0x1234, RD set (flags 0x0100). -/
def queryA : Msg :=
  { header := { id := 0x1234, flags := 0x0100, qdCount := 1, anCount := 0,
                nsCount := 0, arCount := 0 }
    questions := [{ qname := wwwExample, qtype := 1, qclass := 1 }]
    answers := [], authority := [], additional := [] }

/-- An `AAAA` query for `www.example.com`, id 0x1235. -/
def queryAAAA : Msg :=
  { header := { id := 0x1235, flags := 0x0100, qdCount := 1, anCount := 0,
                nsCount := 0, arCount := 0 }
    questions := [{ qname := wwwExample, qtype := 28, qclass := 1 }]
    answers := [], authority := [], additional := [] }

/-- An `A` query for `dn.example.com` — a name the zone does not hold. -/
def queryUnknown : Msg :=
  { header := { id := 0x1236, flags := 0x0100, qdCount := 1, anCount := 0,
                nsCount := 0, arCount := 0 }
    questions := [{ qname := dnExample, qtype := 1, qclass := 1 }]
    answers := [], authority := [], additional := [] }

/-! ## The authoritative peer's response

Flags 0x8500 = QR set, AA set (authoritative), opcode QUERY, RCODE 0
(NoError). The NXDOMAIN response uses RCODE 3 (flags 0x8503) with an empty
answer section, as an authoritative server returns for a name it does not own
(RFC 1035 §4.1.1). -/

/-- Authoritative `A` answer: `www.example.com IN A 93.184.216.34`, TTL 300. -/
def answerA : Msg :=
  { header := { id := 0x1234, flags := 0x8500, qdCount := 1, anCount := 1,
                nsCount := 0, arCount := 0 }
    questions := [{ qname := wwwExample, qtype := 1, qclass := 1 }]
    answers := [⟨{ name := wwwExample, rrType := 1, rrClass := 1, ttl := 300,
                   rdata := zoneA_bytes }, 0⟩]
    authority := [], additional := [] }

/-- Authoritative `AAAA` answer: `www.example.com IN AAAA 2606:4700:10::ac42:93f3`. -/
def answerAAAA : Msg :=
  { header := { id := 0x1235, flags := 0x8500, qdCount := 1, anCount := 1,
                nsCount := 0, arCount := 0 }
    questions := [{ qname := wwwExample, qtype := 28, qclass := 1 }]
    answers := [⟨{ name := wwwExample, rrType := 28, rrClass := 1, ttl := 300,
                   rdata := zoneAAAA_bytes }, 0⟩]
    authority := [], additional := [] }

/-- Authoritative NXDOMAIN for `dn.example.com` (RCODE 3, empty answer). -/
def answerNx : Msg :=
  { header := { id := 0x1236, flags := 0x8503, qdCount := 1, anCount := 0,
                nsCount := 0, arCount := 0 }
    questions := [{ qname := dnExample, qtype := 1, qclass := 1 }]
    answers := [], authority := [], additional := [] }

/-! ## The end-to-end forward-resolution obligations

Each equation runs the REAL pipeline: the authoritative peer's `encodeMsg`
emits wire bytes, the stub's `encodeMsg` emits the query it sent, and
`resolveA` / `resolveAAAA` re-parse both (`Dns.parseMsg`) and extract. All
`decide` — kernel reduction of the deployed functions, no `native_decide`. -/

/-- **A forward resolution.** The `A` query for a zone name resolves to the
zone's proven `A` address, out of the bytes the authoritative peer emitted. -/
theorem forward_resolve_a :
    resolveA (encodeMsg queryA) (encodeMsg answerA) = [zoneA_num] := by decide

/-- **AAAA forward resolution (RFC 3596).** The `AAAA` query resolves to the
zone's proven 128-bit address. -/
theorem forward_resolve_aaaa :
    resolveAAAA (encodeMsg queryAAAA) (encodeMsg answerAAAA) = [zoneAAAA_num] := by decide

/-- **NXDOMAIN.** A query for a name the zone does not hold resolves to `[]`
against the authoritative NXDOMAIN response — not a wrong answer, not a leaked
address. -/
theorem resolve_nxdomain :
    resolveA (encodeMsg queryUnknown) (encodeMsg answerNx) = [] := by decide

/-- **NXDOMAIN does not leak another name's record.** Even the `answerA` wire
bytes (which carry `www.example.com`'s address) answer *nothing* to the
`dn.example.com` query: the question does not echo, so extraction refuses it. A
resolver that returned `answerA`'s address here would be answering the wrong
name. -/
theorem resolve_wrong_name_refused :
    resolveA (encodeMsg queryUnknown) (encodeMsg answerA) = [] := by decide

/-! ## Non-fabrication: every extracted address is backed by a real record

The headline equations are for the zone's own answer. These generalize the
guarantee to arbitrary response bytes: forward resolution never invents an
address — everything it returns came from a real answer record of the queried
type, class IN, in a non-error response. Corollaries of `Dns.answersFor_sound`;
the real hypothesis is the membership of the extracted address. -/

/-- **A extraction is never fabricated.** Any `A` address `answersFor` returns
for an `A` query (qtype 1) is backed by a real type-1, class-IN answer record in
a response whose header RCODE is 0. General over `qid` / `host` / `resp`. -/
theorem forward_resolve_sound (qid : Nat) (host : Name) (resp : Bytes) (addr : Nat)
    (h : RData.a addr ∈ answersFor qid host 1 resp) :
    ∃ m, parseMsg resp = some m
      ∧ m.header.rcode = 0
      ∧ (∃ r ∈ m.answers, r.rr.rrClass = 1 ∧ r.rr.rrType = 1
          ∧ typedRData resp r = some (.a addr)) := by
  obtain ⟨m, hp, _, _, _, _, _, hr0, _, ⟨r, hr, hc, ht, hv⟩⟩ :=
    answersFor_sound qid host 1 resp (.a addr) h
  exact ⟨m, hp, hr0, r, hr, hc, ht, hv⟩

/-- **AAAA extraction is never fabricated.** The type-28 twin of
`forward_resolve_sound`. -/
theorem forward_resolve_aaaa_sound (qid : Nat) (host : Name) (resp : Bytes) (addr : Nat)
    (h : RData.aaaa addr ∈ answersFor qid host 28 resp) :
    ∃ m, parseMsg resp = some m
      ∧ m.header.rcode = 0
      ∧ (∃ r ∈ m.answers, r.rr.rrClass = 1 ∧ r.rr.rrType = 28
          ∧ typedRData resp r = some (.aaaa addr)) := by
  obtain ⟨m, hp, _, _, _, _, _, hr0, _, ⟨r, hr, hc, ht, hv⟩⟩ :=
    answersFor_sound qid host 28 resp (.aaaa addr) h
  exact ⟨m, hp, hr0, r, hr, hc, ht, hv⟩

/-! ## The selftest — forward resolution over real bytes, in one process

Pure (no crypto, no FFI): runs under `lake env lean --run`. It encodes the
query and the authoritative answer with the proven `encodeMsg`, runs the
deployed `resolveA` / `resolveAAAA` over the emitted bytes, and cross-checks the
extracted addresses against the proven values — the running realization of the
`decide` equations above. -/

/-- Dotted-decimal for an A number (for the printout). -/
def a4Str (n : Nat) : String :=
  s!"{n / 16777216 % 256}.{n / 65536 % 256}.{n / 256 % 256}.{n % 256}"

def selftest : IO UInt32 := do
  IO.println "== dns forward-resolve selftest : A/AAAA/NXDOMAIN, byte-level, NO crypto =="
  let mut ok := true

  -- A: encode query + authoritative answer, resolve, cross-check.
  let qA := encodeMsg queryA
  let aA := encodeMsg answerA
  let gotA := resolveA qA aA
  IO.println s!"[A]      www.example.com -> {gotA.map a4Str}  (query {qA.length}B, resp {aA.length}B)"
  if gotA != [zoneA_num] then ok := false; IO.println "  FAIL: A did not resolve to the zone record"

  -- AAAA.
  let qAAAA := encodeMsg queryAAAA
  let aAAAA := encodeMsg answerAAAA
  let gotAAAA := resolveAAAA qAAAA aAAAA
  IO.println s!"[AAAA]   www.example.com -> {gotAAAA}"
  if gotAAAA != [zoneAAAA_num] then ok := false; IO.println "  FAIL: AAAA did not resolve to the zone record"

  -- NXDOMAIN: unknown name against the authoritative NXDOMAIN response.
  let qU := encodeMsg queryUnknown
  let aNx := encodeMsg answerNx
  let gotNx := resolveA qU aNx
  IO.println s!"[NX]     dn.example.com  -> {gotNx.map a4Str}  (RCODE 3)"
  if gotNx != [] then ok := false; IO.println "  FAIL: NXDOMAIN leaked an answer"

  -- Wrong-name refusal: the A answer for www must answer nothing to dn.
  let gotWrong := resolveA qU aA
  IO.println s!"[wrong]  dn query vs www answer -> {gotWrong.map a4Str}  (must be [])"
  if gotWrong != [] then ok := false; IO.println "  FAIL: extracted a wrong-name address"

  if ok then
    IO.println "OK: forward resolution matches the proven records"
    return 0
  else
    IO.println "SELFTEST FAILED"
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["selftest"] => selftest
  | _ => do IO.eprintln "usage: dns-forward-resolve-live selftest"; return 2

end Dns.ForwardResolve

/-- Top-level entry (the `lean_exe` root) forwarding to the namespaced `main`. -/
def main (args : List String) : IO UInt32 := Dns.ForwardResolve.main args
