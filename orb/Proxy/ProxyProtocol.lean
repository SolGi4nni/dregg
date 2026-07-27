/-!
# PROXY protocol v1 (text) and v2 (binary) — client-address recovery

A load balancer that terminates the client TCP connection and opens a fresh
connection to the backend hides the real client address behind its own. The
PROXY protocol restores it: the balancer prepends a small header — the *first*
bytes on the backend connection, ahead of any TLS or HTTP traffic — carrying
the original `(source, destination)` socket addresses. The backend parses that
header and uses the recovered **source** address for IP filtering and access
logging, rather than the balancer's own (destination / peer) address.

Two encodings are modeled:

* **v1** is a human-readable line
  `PROXY <family> <src-ip> <dst-ip> <src-port> <dst-port>\r\n`, e.g.
  `PROXY TCP4 192.168.1.1 10.0.0.1 12345 80\r\n`. Dotted-quad and decimal
  parsing is modeled for real (not assumed): `parseDecimal` folds ASCII digits
  and `parseIPv4` splits on `.` into four in-range octets.
* **v2** is a binary frame: a fixed 12-byte signature, a version/command byte,
  a family/protocol byte, a big-endian 16-bit address-section length, then the
  fixed-width source and destination addresses (4+4+2+2 bytes for IPv4,
  16+16+2+2 for IPv6).

## What is proved

* `proxy_proto_v1_parse` — the canonical v1 `TCP4` line parses to the real
  client address `192.168.1.1:12345` and destination `10.0.0.1:80`, consuming
  exactly the header (a concrete on-the-wire vector, decided by the kernel).
* `proxy_proto_v2_parse` — **general** IPv4 round-trip: for *any* source and
  destination octets and any in-range ports, the v2 frame the balancer emits
  parses back to exactly those two socket addresses, consuming the whole frame.
  `proxy_proto_v2_parse_ipv6` is the IPv6 analogue (source octets of length 16).
* `proxy_proto_recovers_client` — the address the backend feeds to the IP
  filter / access log (`clientAddr = header.src`) is the recovered *client*
  source, is **not** the balancer's destination address, and the destination is
  recovered separately — so filtering and logging key on the client, never the
  balancer's peer address.
* `proxy_proto_v1_reject` / `proxy_proto_v2_reject` — a line that does not begin
  with the `PROXY ` prefix, and a binary frame with a wrong signature, are each
  rejected with the corresponding structured error (malformed input is not
  silently accepted as a client identity).

## Boundary / UNCLOSED

* v1 IPv6 (`TCP6`) textual address parsing (`::` compression) is not modeled;
  a `TCP6` v1 line is reported `unsupportedV1Family`. v2 IPv6 is fully modeled.
* v2 TLV (type-length-value) extensions are carried on the wire but are not
  reconstructed into the parsed header here (the recovered `tlvs` is `[]`); the
  address-recovery theorems are unaffected.
* Streaming `incomplete` boundaries (partial signature / missing CRLF) are
  classified by the parser but not the subject of the correctness theorems.
-/

namespace Proxy.ProxyProtocol

/-- A raw byte buffer. -/
abbrev Bytes := List UInt8

/-- A recovered IP address: an IPv4 quad, or an IPv6 octet string (16 bytes). -/
inductive IpAddr where
  | v4 (a b c d : UInt8)
  | v6 (octets : Bytes)
deriving Repr, DecidableEq

/-- A socket address: an IP plus a 16-bit port (modeled as `Nat`, in range). -/
structure SockAddr where
  ip : IpAddr
  port : Nat
deriving Repr, DecidableEq

/-- A parsed PROXY header. `src`/`dst` are `none` for `LOCAL` / `UNKNOWN`
(health-check) headers that carry no addresses. -/
structure Header where
  src : Option SockAddr
  dst : Option SockAddr
  version : Nat
  tlvs : List (UInt8 × Bytes)
deriving Repr, DecidableEq

/-- Structured parse errors (one per malformed-input class). -/
inductive ParseErr where
  | lineTooLong
  | invalidV1Format
  | invalidAddress
  | invalidPort
  | unsupportedV1Family
  | invalidV2Signature
  | invalidV2VersionCommand
  | invalidV2Family
  | v2AddressTruncated
  | notProxyProtocol
deriving Repr, DecidableEq

/-- Outcome of a parse attempt: a complete header (with bytes consumed), a
request for more bytes, or a structured protocol error. -/
inductive ParseResult where
  | complete (header : Header) (consumed : Nat)
  | incomplete
  | invalid (err : ParseErr)
deriving Repr, DecidableEq

/-- The address the backend uses for IP filtering and access logging: the
recovered **client source**, never the balancer's destination/peer address. -/
def clientAddr (h : Header) : Option SockAddr := h.src

/-! ## Byte-level helpers -/

/-- Encode a value `< 65536` as two big-endian bytes. -/
def enc16 (n : Nat) : Bytes := [UInt8.ofNat (n / 256 % 256), UInt8.ofNat (n % 256)]

/-- Decode two big-endian bytes to a `Nat`. -/
def be16 (hi lo : UInt8) : Nat := hi.toNat * 256 + lo.toNat

/-- A big-endian 16-bit value round-trips through `enc16` when it is in range. -/
theorem be16_enc16 (n : Nat) (h : n < 65536) :
    be16 (UInt8.ofNat (n / 256 % 256)) (UInt8.ofNat (n % 256)) = n := by
  simp only [be16, UInt8.toNat_ofNat']
  omega

/-! ## v1 (text) parser -/

/-- Is `b` an ASCII decimal digit `0`–`9`? -/
def isDigit (b : UInt8) : Bool := decide (0x30 ≤ b.toNat ∧ b.toNat ≤ 0x39)

/-- Decode a non-empty run of ASCII decimal digits to a `Nat`; `none` on an
empty run or any non-digit byte. -/
def parseDecimal (bs : Bytes) : Option Nat :=
  match bs with
  | [] => none
  | _ =>
    bs.foldl (fun acc b =>
      match acc with
      | none => none
      | some n => if isDigit b then some (n * 10 + (b.toNat - 0x30)) else none) (some 0)

/-- Split `bs` on the separator byte `sep` (like `str.split`). -/
def splitOn (sep : UInt8) : Bytes → List Bytes
  | [] => [[]]
  | b :: bs =>
    let rest := splitOn sep bs
    if b == sep then [] :: rest
    else match rest with
      | [] => [[b]]
      | cur :: more => (b :: cur) :: more

/-- Parse a dotted-quad IPv4 literal into an `IpAddr`. -/
def parseIPv4 (bs : Bytes) : Option IpAddr :=
  match splitOn 0x2E bs with
  | [p0, p1, p2, p3] =>
    match parseDecimal p0, parseDecimal p1, parseDecimal p2, parseDecimal p3 with
    | some a, some b, some c, some d =>
      if a < 256 ∧ b < 256 ∧ c < 256 ∧ d < 256 then
        some (.v4 (UInt8.ofNat a) (UInt8.ofNat b) (UInt8.ofNat c) (UInt8.ofNat d))
      else none
    | _, _, _, _ => none
  | _ => none

/-- Position of the first `\r\n` (CR then LF) in `bs`, if any. -/
def findCRLF : Bytes → Option Nat
  | [] => none
  | [_] => none
  | b0 :: b1 :: rest =>
    if b0 == 0x0D ∧ b1 == 0x0A then some 0
    else (findCRLF (b1 :: rest)).map (· + 1)

/-- The 6-byte v1 prefix `"PROXY "`. -/
def v1Prefix : Bytes := [0x50, 0x52, 0x4F, 0x58, 0x59, 0x20]

/-- Parse a PROXY protocol v1 (text) header. -/
def parseV1 (buf : Bytes) : ParseResult :=
  if buf.take 6 ≠ v1Prefix then
    if v1Prefix.take buf.length == buf then .incomplete
    else .invalid .invalidV1Format
  else
    match findCRLF buf with
    | none => if buf.length > 107 then .invalid .lineTooLong else .incomplete
    | some pos =>
      let line := buf.take pos
      let consumed := pos + 2
      match splitOn 0x20 line with
      | _ :: fam :: rest =>
        -- `PROXY UNKNOWN ...` — health check, no addresses.
        if fam == [0x55, 0x4E, 0x4B, 0x4E, 0x4F, 0x57, 0x4E] then
          .complete ⟨none, none, 1, []⟩ consumed
        else
          match rest with
          | [srcIp, dstIp, srcP, dstP] =>
            if fam == [0x54, 0x43, 0x50, 0x34] then
              -- TCP4
              match parseIPv4 srcIp, parseIPv4 dstIp, parseDecimal srcP, parseDecimal dstP with
              | some s, some d, some sp, some dp =>
                if sp < 65536 ∧ dp < 65536 then
                  .complete ⟨some ⟨s, sp⟩, some ⟨d, dp⟩, 1, []⟩ consumed
                else .invalid .invalidPort
              | _, _, _, _ => .invalid .invalidAddress
            else if fam == [0x54, 0x43, 0x50, 0x36] then
              -- TCP6 textual parsing is not modeled.
              .invalid .unsupportedV1Family
            else .invalid .unsupportedV1Family
          | _ => .invalid .invalidV1Format
      | _ => .invalid .invalidV1Format

/-! ## v2 (binary) parser and encoder -/

/-- The fixed 12-byte v2 signature. -/
def v2Signature : Bytes :=
  [0x0D, 0x0A, 0x0D, 0x0A, 0x00, 0x0D, 0x0A, 0x51, 0x55, 0x49, 0x54, 0x0A]

/-- The address bytes for an IP: the four octets for v4, the stored octet
string for v6. -/
def octetsOf : IpAddr → Bytes
  | .v4 a b c d => [a, b, c, d]
  | .v6 o => o

/-- Family/protocol byte: AF_INET+STREAM (`0x11`) or AF_INET6+STREAM (`0x21`). -/
def famProtoOf : IpAddr → UInt8
  | .v4 .. => 0x11
  | .v6 .. => 0x21

/-- The v2 address section for a proxied connection: source octets, destination
octets, source port, destination port. -/
def v2AddrSection (src dst : SockAddr) : Bytes :=
  octetsOf src.ip ++ octetsOf dst.ip ++ enc16 src.port ++ enc16 dst.port

/-- Encode a v2 `PROXY` (command `1`) header for `src`/`dst` (assumed same
family; the family byte follows `src`). -/
def encodeV2Proxy (src dst : SockAddr) : Bytes :=
  v2Signature ++ [0x21, famProtoOf src.ip]
    ++ enc16 (v2AddrSection src dst).length ++ v2AddrSection src dst

/-- Parse a PROXY protocol v2 (binary) header. -/
def parseV2 (buf : Bytes) : ParseResult :=
  if buf.length < 16 then
    let k := min buf.length 12
    if v2Signature.take k == buf.take k then .incomplete
    else .invalid .invalidV2Signature
  else if buf.take 12 ≠ v2Signature then .invalid .invalidV2Signature
  else
    let verCmd := (buf.getD 12 0).toNat
    let version := verCmd / 16
    let command := verCmd % 16
    let family := (buf.getD 13 0).toNat / 16
    let addrLen := be16 (buf.getD 14 0) (buf.getD 15 0)
    if version ≠ 2 then .invalid .invalidV2VersionCommand
    else if command > 1 then .invalid .invalidV2VersionCommand
    else if buf.length < 16 + addrLen then .incomplete
    else
      let addrData := (buf.drop 16).take addrLen
      let consumed := 16 + addrLen
      if command = 0 then .complete ⟨none, none, 2, []⟩ consumed
      else
        match family with
        | 0 => .complete ⟨none, none, 2, []⟩ consumed
        | 1 =>
          if addrData.length < 12 then .invalid .v2AddressTruncated
          else
            .complete
              ⟨some ⟨.v4 (addrData.getD 0 0) (addrData.getD 1 0)
                        (addrData.getD 2 0) (addrData.getD 3 0),
                     be16 (addrData.getD 8 0) (addrData.getD 9 0)⟩,
               some ⟨.v4 (addrData.getD 4 0) (addrData.getD 5 0)
                        (addrData.getD 6 0) (addrData.getD 7 0),
                     be16 (addrData.getD 10 0) (addrData.getD 11 0)⟩,
               2, []⟩ consumed
        | 2 =>
          if addrData.length < 36 then .invalid .v2AddressTruncated
          else
            .complete
              ⟨some ⟨.v6 (addrData.take 16),
                     be16 (addrData.getD 32 0) (addrData.getD 33 0)⟩,
               some ⟨.v6 ((addrData.drop 16).take 16),
                     be16 (addrData.getD 34 0) (addrData.getD 35 0)⟩,
               2, []⟩ consumed
        | _ => .invalid .invalidV2Family

/-! ## Theorems -/

/-- The canonical v1 `TCP4` line `PROXY TCP4 192.168.1.1 10.0.0.1 12345 80\r\n`
(42 bytes on the wire). -/
def sampleV1 : Bytes :=
  [80, 82, 79, 88, 89, 32,
   84, 67, 80, 52, 32,
   49, 57, 50, 46, 49, 54, 56, 46, 49, 46, 49, 32,
   49, 48, 46, 48, 46, 48, 46, 49, 32,
   49, 50, 51, 52, 53, 32,
   56, 48,
   13, 10]

/-- **v1 parse (PROXY protocol v1, text).** The canonical `TCP4` line parses to the
real client `192.168.1.1:12345` and destination `10.0.0.1:80`, consuming
exactly the 42-byte header. Non-vacuous: an on-the-wire byte vector decodes to
the concrete recovered addresses. -/
theorem proxy_proto_v1_parse :
    parseV1 sampleV1 =
      .complete ⟨some ⟨.v4 192 168 1 1, 12345⟩,
                 some ⟨.v4 10 0 0 1, 80⟩, 1, []⟩ 42 := by
  decide

/-- IPv4 v2 round-trip lemma: the frame emitted for `src`/`dst` (both v4) parses
back to exactly those socket addresses, consuming the whole 28-byte frame. -/
theorem parseV2_encodeV2Proxy_v4
    (a b c d e f g h : UInt8) (sp dp : Nat)
    (hsp : sp < 65536) (hdp : dp < 65536) :
    parseV2 (encodeV2Proxy ⟨.v4 a b c d, sp⟩ ⟨.v4 e f g h, dp⟩) =
      .complete ⟨some ⟨.v4 a b c d, sp⟩, some ⟨.v4 e f g h, dp⟩, 2, []⟩ 28 := by
  simp only [encodeV2Proxy, v2AddrSection, octetsOf, famProtoOf, enc16, v2Signature,
        parseV2, be16, UInt8.toNat_ofNat, List.getD_cons_zero, List.getD_cons_succ]
  simp
  omega

/-- **v2 parse (PROXY protocol v2, IPv4).** General round-trip: for any source
and destination octets and any in-range ports, the binary frame the balancer
emits parses back to exactly the encoded client and destination socket
addresses. Non-vacuous: quantified over all addresses/ports with the real
in-range hypotheses, not a fixed vector. -/
theorem proxy_proto_v2_parse
    (a b c d e f g h : UInt8) (sp dp : Nat)
    (hsp : sp < 65536) (hdp : dp < 65536) :
    parseV2 (encodeV2Proxy ⟨.v4 a b c d, sp⟩ ⟨.v4 e f g h, dp⟩) =
      .complete ⟨some ⟨.v4 a b c d, sp⟩, some ⟨.v4 e f g h, dp⟩, 2, []⟩ 28 :=
  parseV2_encodeV2Proxy_v4 a b c d e f g h sp dp hsp hdp

/-- **v2 parse (PROXY protocol v2, IPv6).** The IPv6 analogue: a v2 frame for
16-byte source/destination octets round-trips to those addresses. -/
theorem proxy_proto_v2_parse_ipv6
    (so do' : Bytes) (sp dp : Nat)
    (hso : so.length = 16) (hdo : do'.length = 16)
    (hsp : sp < 65536) (hdp : dp < 65536) :
    parseV2 (encodeV2Proxy ⟨.v6 so, sp⟩ ⟨.v6 do', dp⟩) =
      .complete ⟨some ⟨.v6 so, sp⟩, some ⟨.v6 do', dp⟩, 2, []⟩ 52 := by
  -- Expose the 16-byte octet strings as explicit cons cells.
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, rfl⟩ :
      ∃ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15,
        so = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] := by
    match so, hso with
    | [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15], _ =>
      exact ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, rfl⟩
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, rfl⟩ :
      ∃ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15,
        do' = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] := by
    match do', hdo with
    | [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15], _ =>
      exact ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, rfl⟩
  simp only [encodeV2Proxy, v2AddrSection, octetsOf, famProtoOf, enc16, v2Signature,
        parseV2, be16, UInt8.toNat_ofNat, List.getD_cons_zero, List.getD_cons_succ]
  simp
  omega

/-- **Client recovery.** The address the backend feeds to the IP filter and the
access log (`clientAddr = header.src`) is the recovered client *source*; it is
**not** the balancer's destination address; and the destination is recovered
separately. So filtering and logging key on the real client, never the
balancer's peer. Hypotheses are the real in-range port bounds plus a genuine
`src ≠ dst`; the conclusion is not a tautology. -/
theorem proxy_proto_recovers_client
    (a b c d e f g h : UInt8) (sp dp : Nat)
    (hsp : sp < 65536) (hdp : dp < 65536)
    (hne : (⟨.v4 a b c d, sp⟩ : SockAddr) ≠ ⟨.v4 e f g h, dp⟩) :
    ∃ hdr n,
      parseV2 (encodeV2Proxy ⟨.v4 a b c d, sp⟩ ⟨.v4 e f g h, dp⟩) = .complete hdr n ∧
      clientAddr hdr = some ⟨.v4 a b c d, sp⟩ ∧
      clientAddr hdr ≠ hdr.dst ∧
      hdr.dst = some ⟨.v4 e f g h, dp⟩ := by
  refine ⟨_, _, parseV2_encodeV2Proxy_v4 a b c d e f g h sp dp hsp hdp, rfl, ?_, rfl⟩
  simp only [clientAddr]
  intro hcontra
  exact hne (Option.some.inj hcontra)

/-- A line that does not begin with the `PROXY ` prefix is rejected. -/
def sampleBadV1 : Bytes := [71, 69, 84, 32, 47, 32, 13, 10]  -- "GET / \r\n"

/-- **Malformed v1 reject.** Non-PROXY input is not accepted as a client
identity — it is a structured `invalidV1Format` error. -/
theorem proxy_proto_v1_reject :
    parseV1 sampleBadV1 = .invalid .invalidV1Format := by decide

/-- A 16-byte binary frame with a wrong signature. -/
def sampleBadV2 : Bytes := List.replicate 16 0xFF

/-- **Malformed v2 reject.** A frame whose 12-byte signature is wrong is
rejected with `invalidV2Signature`, not decoded into a bogus address. -/
theorem proxy_proto_v2_reject :
    parseV2 sampleBadV2 = .invalid .invalidV2Signature := by decide

end Proxy.ProxyProtocol
