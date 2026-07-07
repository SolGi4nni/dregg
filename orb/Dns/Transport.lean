import Dns.Resolve

/-!
# TCP transport framing and the truncation retry (RFC 1035 §4.2.2, RFC 7766)

Over TCP, "the message is prefixed with a two byte length field which gives
the message length, excluding the two byte length field" (RFC 1035 §4.2.2).
And over UDP, a response with TC set tells the resolver its answer was cut to
fit the transport: RFC 7766 §5 (following §4.2.1) has the client retry the
query over TCP. `Dns.answersFor` already *refuses* a TC response
(`answersFor_tc`); this file models the follow-up:

* `frameTcp` / `unframeTcp` — the §4.2.2 length prefix, with an exact
  roundtrip theorem;
* `wantsTcpRetryOf` — the retry predicate: the UDP response is a genuine
  reply to *this* query (ID, QR, opcode, question echoed under the §2.3.3
  comparison) but truncated;
* `resolveUdpThenTcp` — the composed resolution: consume the UDP response
  unless it demands the TCP retry, in which case extract from the unframed
  TCP response instead. Soundness reduces to `answersFor_sound` on whichever
  transport's bytes were consumed.
-/

namespace Dns

/-! ## The two-octet length prefix (RFC 1035 §4.2.2) -/

/-- Frame one message for TCP: big-endian length, then the message. -/
def frameTcp (m : Bytes) : Bytes := putU16 m.length ++ m

/-- Unframe one message from a TCP stream: reads the length prefix, returns
the message and the remaining stream octets. `none` when the stream is shorter
than its own prefix claims. -/
def unframeTcp (s : Bytes) : Option (Bytes × Bytes) :=
  match s with
  | l1 :: l2 :: rest =>
    if be16 l1 l2 ≤ rest.length then
      some (rest.take (be16 l1 l2), rest.drop (be16 l1 l2))
    else none
  | _ => none

/-- **The framing roundtrip.** A framed message (length < 2^16, which §4.2.2's
16-bit prefix forces) unframes to exactly itself, leaving exactly the rest of
the stream — framing is prefix-free, so messages can be concatenated. -/
theorem unframeTcp_frameTcp (m rest : Bytes) (h : m.length < 65536) :
    unframeTcp (frameTcp m ++ rest) = some (m, rest) := by
  have hcons : frameTcp m ++ rest
      = UInt8.ofNat (m.length / 256) :: UInt8.ofNat m.length :: (m ++ rest) := by
    simp [frameTcp, putU16]
  rw [hcons]
  unfold unframeTcp
  dsimp only
  rw [be16_putU16 m.length h]
  rw [if_pos (by simp [List.length_append])]
  rw [List.take_left m rest, List.drop_left m rest]

/-- The prefix is load-bearing: a stream shorter than its prefix claims does
not unframe. -/
theorem unframeTcp_short (l1 l2 : UInt8) (rest : Bytes)
    (h : rest.length < be16 l1 l2) : unframeTcp (l1 :: l2 :: rest) = none := by
  unfold unframeTcp
  dsimp only
  rw [if_neg (by omega)]

/-- Unframing is total and structural: what comes back is a take/drop split of
the stream past its prefix. -/
theorem unframeTcp_split (s m rest : Bytes) (h : unframeTcp s = some (m, rest)) :
    ∃ l1 l2 tail, s = l1 :: l2 :: tail ∧ m.length = be16 l1 l2
      ∧ m ++ rest = tail := by
  unfold unframeTcp at h
  split at h
  · rename_i l1 l2 tail
    split at h
    · rename_i hle
      injection h with h
      injection h with hm hr
      subst hm; subst hr
      exact ⟨l1, l2, tail, rfl, by rw [List.length_take]; omega,
             List.take_append_drop _ _⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-! ## The truncation retry (RFC 1035 §4.2.1 / RFC 7766 §5) -/

/-- Does this response demand a TCP retry of the question `(host, qtype)`
asked under `qid`? Exactly like `matchesQuery` — a genuine reply to this very
query — except TC is *required* (and the RCODE is not consulted: §4.2.2 retry
happens on truncation, whatever the partial RCODE says). -/
def wantsTcpRetry (qid : Nat) (host : Name) (qtype : Nat) (resp : Bytes) : Bool :=
  match parseMsg resp with
  | none => false
  | some m =>
    m.header.id == qid
      && m.header.qr
      && m.header.opcode == 0
      && m.header.tc
      && match m.questions with
         | [q] => nameEq q.qname host && q.qtype == qtype && q.qclass == 1
         | _ => false

/-- Query-driven form: read the ID and question out of the real query bytes. -/
def wantsTcpRetryOf (query resp : Bytes) : Bool :=
  match parseMsg query with
  | none => false
  | some qm =>
    match qm.questions with
    | [q] =>
      !qm.header.qr && q.qclass == 1
        && wantsTcpRetry qm.header.id q.qname q.qtype resp
    | _ => false

/-- Extraction over a framed TCP stream: unframe the first message, extract
from it. -/
def answersOfTcp (query stream : Bytes) : List RData :=
  match unframeTcp stream with
  | none => []
  | some (resp, _) => answersOf query resp

/-- **The composed resolution.** Consume the UDP response — unless it is a
truncated reply to this query, in which case consume the (framed) TCP
response instead. -/
def resolveUdpThenTcp (query udpResp tcpStream : Bytes) : List RData :=
  if wantsTcpRetryOf query udpResp then answersOfTcp query tcpStream
  else answersOf query udpResp

/-- A retry-demanding response really is a parsed, truncated reply. -/
theorem wantsTcpRetry_tc (qid : Nat) (host : Name) (qtype : Nat) (resp : Bytes)
    (h : wantsTcpRetry qid host qtype resp = true) :
    ∃ m, parseMsg resp = some m ∧ m.header.tc = true := by
  unfold wantsTcpRetry at h
  split at h
  · exact absurd h (by simp)
  · rename_i m hm
    simp only [Bool.and_eq_true] at h
    exact ⟨m, hm, h.1.2⟩

/-- **Retry and consume are mutually exclusive.** A response that demands the
TCP retry contributes no answers itself — there is no path on which a
truncated body is both retried and consumed. -/
theorem wantsTcpRetry_excludes (qid : Nat) (host : Name) (qtype : Nat)
    (resp : Bytes) (h : wantsTcpRetry qid host qtype resp = true) :
    answersFor qid host qtype resp = [] := by
  obtain ⟨m, hm, htc⟩ := wantsTcpRetry_tc qid host qtype resp h
  exact answersFor_tc qid host qtype resp m hm htc

/-- **Composed soundness.** Every answer the composed resolution returns went
through `answersOf` — hence `answersFor_sound` — against either the UDP bytes
or the message unframed from the TCP stream; nothing else is ever consumed. -/
theorem resolveUdpThenTcp_sound (query udpResp tcpStream : Bytes) (d : RData)
    (hd : d ∈ resolveUdpThenTcp query udpResp tcpStream) :
    d ∈ answersOf query udpResp
      ∨ ∃ resp rest, unframeTcp tcpStream = some (resp, rest)
          ∧ d ∈ answersOf query resp := by
  unfold resolveUdpThenTcp at hd
  split at hd
  · unfold answersOfTcp at hd
    split at hd
    · simp at hd
    · rename_i resp rst hu
      exact Or.inr ⟨resp, rst, hu, hd⟩
  · exact Or.inl hd

/-! ## Worked wire vectors, kernel-checked -/

/-- A truncated reply to `qUp` (flags 0x8380: QR, TC, RD, RA) carrying a
partial answer record. -/
def rUpTc : Bytes :=
  [ 0x12, 0x34, 0x83, 0x80, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00,
    2, 117, 112, 0, 0x00, 0x01, 0x00, 0x01,
    2, 117, 112, 0, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x3C, 0x00, 0x04,
    93, 184, 216, 34 ]

/-- The complete reply, as it would arrive over TCP. -/
def rUpFull : Bytes :=
  [ 0x12, 0x34, 0x81, 0x80, 0x00, 0x01, 0x00, 0x02, 0x00, 0x00, 0x00, 0x00,
    2, 117, 112, 0, 0x00, 0x01, 0x00, 0x01,
    2, 117, 112, 0, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x3C, 0x00, 0x04,
    93, 184, 216, 34,
    2, 117, 112, 0, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x3C, 0x00, 0x04,
    10, 0, 0, 7 ]

/-- The truncated response is refused outright… -/
theorem resolveA_tc_refused : resolveA qUp rUpTc = [] := by decide

/-- …and demands the retry… -/
theorem tc_wants_retry : wantsTcpRetryOf qUp rUpTc = true := by decide

/-- …while a complete response demands none. -/
theorem complete_wants_no_retry : wantsTcpRetryOf qUp rUpCname = false := by decide

/-- **The full §4.2.2 path on wire bytes**: UDP reply truncated → retry →
unframe the TCP stream → both A records extracted from the complete reply. -/
theorem resolveUdpThenTcp_vector :
    (resolveUdpThenTcp qUp rUpTc (frameTcp rUpFull)).filterMap
        (fun d => match d with | .a a => some a | _ => none)
      = [1572395042, 167772167] := by decide

/-- Framing roundtrip on those very bytes, concatenated with a second framed
message: the split is exact. -/
example : unframeTcp (frameTcp rUpFull ++ frameTcp rUpTc)
    = some (rUpFull, frameTcp rUpTc) := by decide

end Dns
