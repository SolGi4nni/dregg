import Dns.Transport

/-!
# DNS-over-TLS (RFC 7858) — the length-prefixed framing, proven

DoT sends DNS messages over a TLS connection. RFC 7858 §3.3 fixes the framing:
"all messages … are sent over a TCP connection [and] the two-octet length field
described in Section 4.2.2 of [RFC1035] MUST be used" — i.e. the exact
`DNS-over-TCP` framing (a big-endian 2-octet length, then the message), now
carried inside the TLS record layer instead of raw TCP.

drorb already proves that single-message framing round-trips
(`Dns.unframeTcp_frameTcp`). DoT runs a *stream* of such messages down one
connection (RFC 7766 pipelining, permitted for DoT by RFC 7858 §3.3), so this
module lifts the framing to a stream: `frameAll` concatenates framed messages,
`deframe` walks a byte stream pulling off complete messages and stopping at a
partial tail, and the round-trip theorems cover **multiple** messages and a
**partial** final message (the continuation case a real reader must handle).

## What is proven

* `dot_framing_roundtrip` — **the headline.** A stream of well-sized DNS
  messages framed by `frameAll` deframes back to exactly that list, with no
  leftover bytes (`deframe … = (msgs, [])`).
* `dot_framing_partial` — a full-frames-plus-truncated-tail stream deframes to
  the complete messages, leaving the partial tail intact for continuation.
* `dot_framing_single` — the one-message case (RFC 1035 §4.2.2 prefix), reusing
  `Dns.unframeTcp_frameTcp`.
* `dot_payload_is_dns` — the framed payload is exactly the proven DNS message:
  deframing a framed query, then `Dns.parseMsg`, yields the same message as
  parsing the query directly.
* `dotExample_*` — non-vacuity on a real `example.com IN A` query.

0 sorries; axioms ⊆ `{propext, Quot.sound, Classical.choice}`. Strictly beyond
the reference DNS client (plain UDP/TCP only — no DoT).
-/

namespace Dns
namespace Dot

/-! ## The framing, lifted to a stream -/

/-- Frame one DNS message for DoT: the RFC 1035 §4.2.2 two-octet length prefix,
then the message — identical to DNS-over-TCP, now inside TLS. -/
def frame (m : Bytes) : Bytes := frameTcp m

/-- Deframe one message from the stream: read the length prefix, return the
message and the remaining stream. `none` on a short/partial prefix. -/
def deframe1 (s : Bytes) : Option (Bytes × Bytes) := unframeTcp s

/-- Frame a whole pipeline of DNS messages: the framed messages concatenated. -/
def frameAll (ms : List Bytes) : Bytes := (ms.map frame).flatten

/-- **Stream deframer.** Pull complete length-prefixed messages off the stream
until a partial/short frame is hit; return the complete messages and the
leftover bytes (a partial final frame, kept for continuation). `fuel` bounds the
walk — one unit per message; `frameAll`-sized streams need `ms.length` (+1 to
observe a partial tail). -/
def deframe : Nat → Bytes → (List Bytes × Bytes)
  | 0, s => ([], s)
  | fuel + 1, s =>
    match unframeTcp s with
    | none => ([], s)
    | some (m, rest) => (m :: (deframe fuel rest).1, (deframe fuel rest).2)

/-- Deframe step, no message available: the whole stream is the leftover. -/
theorem deframe_succ_none (fuel : Nat) (s : Bytes) (h : unframeTcp s = none) :
    deframe (fuel + 1) s = ([], s) := by
  simp only [deframe, h]

/-- Deframe step, one message pulled: cons it and recurse on the rest. -/
theorem deframe_succ_some (fuel : Nat) (s m rest : Bytes)
    (h : unframeTcp s = some (m, rest)) :
    deframe (fuel + 1) s = (m :: (deframe fuel rest).1, (deframe fuel rest).2) := by
  simp only [deframe, h]

/-! ## Round-trip: multiple messages -/

/-- **The DoT framing round-trip (multiple messages).** A stream of DNS messages
(each `< 2^16` octets, as the 16-bit prefix forces) framed by `frameAll`
deframes back to exactly those messages, consuming the whole stream. -/
theorem dot_framing_roundtrip (ms : List Bytes) (h : ∀ m ∈ ms, m.length < 65536) :
    deframe ms.length (frameAll ms) = (ms, []) := by
  induction ms with
  | nil => rfl
  | cons m rest ih =>
    have hm : m.length < 65536 := h m (by simp)
    have hrest : ∀ m' ∈ rest, m'.length < 65536 := fun m' hm' => h m' (by simp [hm'])
    have hframe : frameAll (m :: rest) = frameTcp m ++ frameAll rest := by
      simp [frameAll, frame]
    show deframe (rest.length + 1) (frameAll (m :: rest)) = _
    rw [hframe,
        deframe_succ_some rest.length (frameTcp m ++ frameAll rest) m (frameAll rest)
          (unframeTcp_frameTcp m (frameAll rest) hm),
        ih hrest]

/-! ## Round-trip: a partial final message

A real DoT reader must tolerate a stream that ends mid-frame — TCP/TLS delivers
bytes in arbitrary chunks. `deframe` stops at the partial tail and hands it back
untouched, so the caller resumes once more bytes arrive. -/

/-- **The DoT framing round-trip with a partial tail.** Complete frames followed
by any byte string `p` that does not itself deframe (a truncated frame) deframe
to exactly the complete messages, leaving `p` as the continuation. -/
theorem dot_framing_partial (ms : List Bytes) (p : Bytes)
    (h : ∀ m ∈ ms, m.length < 65536) (hp : unframeTcp p = none) :
    deframe (ms.length + 1) (frameAll ms ++ p) = (ms, p) := by
  induction ms with
  | nil =>
    show deframe (0 + 1) (frameAll [] ++ p) = _
    have : frameAll ([] : List Bytes) ++ p = p := by simp [frameAll]
    rw [this, deframe_succ_none 0 p hp]
  | cons m rest ih =>
    have hm : m.length < 65536 := h m (by simp)
    have hrest : ∀ m' ∈ rest, m'.length < 65536 := fun m' hm' => h m' (by simp [hm'])
    have hframe : frameAll (m :: rest) ++ p = frameTcp m ++ (frameAll rest ++ p) := by
      simp [frameAll, frame, List.append_assoc]
    show deframe (rest.length + 1 + 1) (frameAll (m :: rest) ++ p) = _
    rw [hframe,
        deframe_succ_some (rest.length + 1) (frameTcp m ++ (frameAll rest ++ p)) m
          (frameAll rest ++ p) (unframeTcp_frameTcp m (frameAll rest ++ p) hm),
        ih hrest]

/-! ## Round-trip: a single message (RFC 1035 §4.2.2) -/

/-- The one-message DoT frame round-trips: a framed message (`< 2^16` octets)
followed by any rest deframes to exactly itself, leaving the rest. This is the
RFC 1035 §4.2.2 prefix, reused for RFC 7858. -/
theorem dot_framing_single (m rest : Bytes) (h : m.length < 65536) :
    deframe1 (frame m ++ rest) = some (m, rest) :=
  unframeTcp_frameTcp m rest h

/-! ## The payload is the proven DNS message -/

/-- **The framed payload is exactly the DNS message.** Framing a DNS query then
deframing recovers the query bytes, so `Dns.parseMsg` of the deframed payload is
the same message as parsing the query directly — the DoT transport is
transparent to the DNS codec. -/
theorem dot_payload_is_dns (q rest : Bytes) (h : q.length < 65536)
    (m : Bytes) (hd : deframe1 (frame q ++ rest) = some (m, rest)) :
    parseMsg m = parseMsg q := by
  have : m = q := by
    have := dot_framing_single q rest h
    rw [this] at hd
    injection hd with hd
    injection hd with hm _
    exact hm.symm
  rw [this]

/-! ## Non-vacuity: a real `example.com IN A` query -/

/-- The DNS wire query `example.com IN A`, id `0xABCD`, RD set (flags `0x0100`);
a genuine RFC 1035 §4.1 message (`dotExample_parses`). -/
def qExample : Bytes :=
  [ 0xAB, 0xCD, 0x01, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    7, 101, 120, 97, 109, 112, 108, 101, 3, 99, 111, 109, 0,
    0x00, 0x01, 0x00, 0x01 ]

/-- The query is a well-formed DNS message: one question, `example.com`, A/IN. -/
theorem dotExample_parses :
    parseMsg qExample
      = some
          { header := { id := 0xABCD, flags := 0x0100, qdCount := 1, anCount := 0,
                        nsCount := 0, arCount := 0 }
            questions := [{ qname := [[101, 120, 97, 109, 112, 108, 101], [99, 111, 109]],
                            qtype := 1, qclass := 1 }]
            answers := [], authority := [], additional := [] } := by decide

/-- **DoT framing, on the real query.** The `example.com IN A` query, framed and
deframed on the wire, round-trips to the exact query bytes. -/
theorem dotExample_single : deframe1 (frame qExample ++ []) = some (qExample, []) := by decide

/-- **Two queries pipelined over one DoT connection** deframe back to both. -/
theorem dotExample_stream :
    deframe 2 (frameAll [qExample, qExample]) = ([qExample, qExample], []) := by decide

/-- And the deframed payload parses to the same DNS query. -/
theorem dotExample_payload_is_dns :
    (deframe1 (frame qExample ++ [])).map (fun r => parseMsg r.1) = some (parseMsg qExample) := by
  rw [dotExample_single]; rfl

end Dot
end Dns
