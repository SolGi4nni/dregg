import H3.Varint

/-!
# HTTP/3 Datagrams (RFC 9297) over QUIC DATAGRAM frames (RFC 9221)

An HTTP/3 endpoint that negotiates datagram support exchanges *HTTP Datagrams*
inside QUIC **DATAGRAM** frames (RFC 9221 §4). Two layers stack here:

* **QUIC DATAGRAM frame** (RFC 9221 §4): frame type `0x30` carries its payload
  to the end of the QUIC packet; type `0x31` prefixes an explicit
  QUIC-varint length. The frame payload is opaque to the transport.

* **HTTP/3 Datagram** (RFC 9297 §2.1): the DATAGRAM frame payload is

  ```
  HTTP/3 Datagram {
    Quarter Stream ID (i),
    HTTP Datagram Payload (..),
  }
  ```

  The *Quarter Stream ID* is a QUIC varint holding the associated request
  stream's identifier divided by four. HTTP requests travel on
  client-initiated bidirectional streams, whose stream IDs are always
  `≡ 0 (mod 4)`; encoding `streamId / 4` is a lossless, range-saving
  representation. Hence the request stream ID is `4 · qsid`.

Headline theorems:

* `h3_datagram_encode_decode` — **round-trip**: the Quarter-Stream-ID varint
  plus the HTTP Datagram Payload frames and deframes to exactly the original
  datagram, for any qsid in the varint range and any payload.
* `datagram_qsid_maps` — the Quarter Stream ID maps to the request stream ID
  `4 · qsid`; that stream ID is a valid client-initiated bidirectional stream
  (`≡ 0 mod 4`), and the mapping is invertible.
* `decoded_datagram_stream_id` — ties the two: a deframed datagram's associated
  request stream ID is `4 · qsid` and `≡ 0 (mod 4)`.
* `h3_over_quic_roundtrip` — the full stack: an HTTP/3 Datagram wrapped in a
  QUIC DATAGRAM frame (type `0x31`) deframes end-to-end.

The varint layer is the proven QUIC varint (`H3.Varint`), so every codec here
inherits its round-trip, length-bound, and canonical-form guarantees.
-/

namespace H3
namespace Datagram

/-! ## Quarter-Stream-ID ↔ request-stream-ID mapping (RFC 9297 §2.1) -/

/-- The request stream ID associated with a Quarter Stream ID: `4 · qsid`. -/
def streamIdOfQsid (qsid : Nat) : Nat := 4 * qsid

/-- The Quarter Stream ID for a request stream: `streamId / 4`. -/
def qsidOfStreamId (streamId : Nat) : Nat := streamId / 4

/-! ## The HTTP/3 Datagram (RFC 9297 §2.1) -/

/-- A parsed HTTP/3 Datagram: the Quarter Stream ID and the opaque payload. -/
structure HttpDatagram where
  qsid : Nat
  payload : Bytes
deriving Repr, DecidableEq

/-- The associated request stream ID of a datagram (RFC 9297 §2.1). -/
def HttpDatagram.streamId (d : HttpDatagram) : Nat := streamIdOfQsid d.qsid

/-- Encode an HTTP/3 Datagram payload: the Quarter-Stream-ID varint followed
by the HTTP Datagram Payload. `none` iff the qsid exceeds the varint range. -/
def encHttpDatagram (d : HttpDatagram) : Option Bytes :=
  match Varint.encVarint d.qsid with
  | some qb => some (qb ++ d.payload)
  | none => none

/-- Decode an HTTP/3 Datagram from a QUIC DATAGRAM frame payload: read the
Quarter-Stream-ID varint; the entire remainder is the HTTP Datagram Payload
(RFC 9297 §2.1 — the payload runs to the end of the DATAGRAM frame). -/
def decHttpDatagram (bs : Bytes) : Option HttpDatagram :=
  match Varint.decVarint bs with
  | none => none
  | some (qsid, n) => some { qsid := qsid, payload := bs.drop n }

/-! ## Round-trip (RFC 9297 §2.1) -/

/-- **HTTP/3 Datagram round-trip.** Framing a datagram (Quarter-Stream-ID
varint + payload) and deframing it recovers exactly the original qsid and
payload. -/
theorem h3_datagram_encode_decode (d : HttpDatagram) (bs : Bytes)
    (h : encHttpDatagram d = some bs) : decHttpDatagram bs = some d := by
  unfold encHttpDatagram at h
  split at h
  · rename_i qb hq
    injection h with h
    subst h
    unfold decHttpDatagram
    rw [Varint.decVarint_encVarint d.qsid qb d.payload hq]
    simp only [List.drop_left]
  · exact absurd h (by simp)

/-- The encoder succeeds exactly on datagrams whose qsid is representable —
witnessing that the round-trip's hypothesis is satisfiable (non-vacuous). -/
theorem encHttpDatagram_isSome_iff (d : HttpDatagram) :
    (encHttpDatagram d).isSome ↔ d.qsid ≤ Varint.maxVarint := by
  unfold encHttpDatagram
  rw [← Varint.encVarint_isSome_iff]
  cases hq : Varint.encVarint d.qsid <;> simp [hq]

/-! ## Quarter-Stream-ID mapping theorems (RFC 9297 §2.1) -/

/-- **Quarter-Stream-ID mapping.** The Quarter Stream ID maps to the request
stream ID `4 · qsid`; that stream ID is a valid client-initiated bidirectional
stream (`≡ 0 (mod 4)`); and the mapping is invertible (`streamId / 4` recovers
the qsid). -/
theorem datagram_qsid_maps (qsid : Nat) :
    streamIdOfQsid qsid = 4 * qsid
      ∧ streamIdOfQsid qsid % 4 = 0
      ∧ qsidOfStreamId (streamIdOfQsid qsid) = qsid := by
  refine ⟨rfl, ?_, ?_⟩
  · unfold streamIdOfQsid; omega
  · unfold qsidOfStreamId streamIdOfQsid; omega

/-- Every request stream ID that is a client-initiated bidirectional stream
(`≡ 0 mod 4`) round-trips through the Quarter-Stream-ID representation. -/
theorem qsid_of_bidi_stream (streamId : Nat) (h : streamId % 4 = 0) :
    streamIdOfQsid (qsidOfStreamId streamId) = streamId := by
  unfold streamIdOfQsid qsidOfStreamId; omega

/-- **Deframed datagram's stream ID.** A datagram that frames and deframes
has an associated request stream ID equal to `4 · qsid` and `≡ 0 (mod 4)` —
the property the H3-datagram handler dispatches on. -/
theorem decoded_datagram_stream_id (d : HttpDatagram) (bs : Bytes)
    (h : encHttpDatagram d = some bs) :
    ∃ d', decHttpDatagram bs = some d'
      ∧ d'.streamId = 4 * d.qsid ∧ d'.streamId % 4 = 0 := by
  refine ⟨d, h3_datagram_encode_decode d bs h, ?_, ?_⟩
  · unfold HttpDatagram.streamId streamIdOfQsid; rfl
  · unfold HttpDatagram.streamId streamIdOfQsid; omega

/-! ## QUIC DATAGRAM frame (RFC 9221 §4) -/

/-- QUIC DATAGRAM frame type without a length field (payload to end of packet). -/
def dgramTypeNoLen : Nat := 0x30

/-- QUIC DATAGRAM frame type with an explicit length varint. -/
def dgramTypeWithLen : Nat := 0x31

/-- Encode the *body* of a length-prefixed QUIC DATAGRAM frame (type `0x31`):
the payload-length varint followed by the payload. (The one-byte frame type
`0x31` precedes this on the wire.) `none` iff the length exceeds varint range —
never for real datagrams (payloads are bounded by the QUIC MTU). -/
def encQuicDatagramLen (payload : Bytes) : Option Bytes :=
  match Varint.encVarint payload.length with
  | some lb => some (lb ++ payload)
  | none => none

/-- Decode a QUIC DATAGRAM frame body given its already-read frame type and the
post-type bytes `bs` (RFC 9221 §4). Type `0x30`: the whole remainder is the
payload. Type `0x31`: a length varint then that many payload bytes. Returns the
payload and the number of post-type bytes consumed; `none` on an unknown type
or a truncated length-prefixed body. -/
def decQuicDatagram (frameType : Nat) (bs : Bytes) : Option (Bytes × Nat) :=
  if frameType = dgramTypeNoLen then
    some (bs, bs.length)
  else if frameType = dgramTypeWithLen then
    match Varint.decVarint bs with
    | none => none
    | some (len, n) =>
      if len ≤ (bs.drop n).length then some ((bs.drop n).take len, n + len)
      else none
  else none

/-- **QUIC DATAGRAM frame round-trip** (type `0x31`). The length-prefixed body
deframes to exactly the payload, consuming the whole body. -/
theorem quic_datagram_len_roundtrip (payload : Bytes) (bs : Bytes)
    (h : encQuicDatagramLen payload = some bs) :
    decQuicDatagram dgramTypeWithLen bs = some (payload, bs.length) := by
  unfold encQuicDatagramLen at h
  split at h
  · rename_i lb hlb
    injection h with h
    subst h
    unfold decQuicDatagram
    rw [if_neg (by decide), if_pos rfl,
        Varint.decVarint_encVarint payload.length lb payload hlb]
    simp only [List.drop_left]
    rw [if_pos (by simp), List.take_length, List.length_append]
  · exact absurd h (by simp)

/-- The type-`0x30` (no-length) QUIC DATAGRAM decode returns the whole
remainder as payload, consuming every byte — the RFC 9221 §4 "to end of
packet" rule. -/
theorem quic_datagram_nolen_decode (bs : Bytes) :
    decQuicDatagram dgramTypeNoLen bs = some (bs, bs.length) := by
  unfold decQuicDatagram
  rw [if_pos rfl]

/-! ## Full stack: HTTP/3 Datagram over a QUIC DATAGRAM frame -/

/-- Encode an HTTP/3 Datagram inside a length-prefixed QUIC DATAGRAM frame
body (type `0x31`). -/
def encH3OverQuic (d : HttpDatagram) : Option Bytes :=
  match encHttpDatagram d with
  | some inner => encQuicDatagramLen inner
  | none => none

/-- Decode an HTTP/3 Datagram from a length-prefixed QUIC DATAGRAM frame body. -/
def decH3OverQuic (bs : Bytes) : Option HttpDatagram :=
  match decQuicDatagram dgramTypeWithLen bs with
  | none => none
  | some (inner, _) => decHttpDatagram inner

/-- **End-to-end round-trip.** An HTTP/3 Datagram wrapped in a QUIC DATAGRAM
frame (type `0x31`) deframes through both layers back to the original
datagram. -/
theorem h3_over_quic_roundtrip (d : HttpDatagram) (bs : Bytes)
    (h : encH3OverQuic d = some bs) : decH3OverQuic bs = some d := by
  unfold encH3OverQuic at h
  split at h
  · rename_i inner hinner
    unfold decH3OverQuic
    rw [quic_datagram_len_roundtrip inner bs h]
    exact h3_datagram_encode_decode d inner hinner
  · exact absurd h (by simp)

/-! ## Framing shape (RFC 9297 §2.1)

The three named semantics of an HTTP/3 datagram, stated directly:

* `h3_datagram_frames` — the wire shape *is* a Quarter-Stream-ID varint
  concatenated with the payload, nothing else.
* `h3_datagram_flow_id` — the Quarter Stream ID (the datagram's *flow id*)
  designates the associated request stream `4 · flowId`, a client-initiated
  bidirectional stream, and the map is invertible.
* `h3_datagram_unreliable` — the delivery semantic: datagrams may be dropped
  (not retransmitted) and reordered (no ordering guarantee), while never
  fabricated.
-/

/-- **Framing shape.** An HTTP/3 Datagram frames to exactly the
Quarter-Stream-ID varint followed by the payload (RFC 9297 §2.1) — no length
field, no trailer; the payload runs to the end of the DATAGRAM frame. Stated
for any qsid whose varint encoding exists (`hq`), which is precisely the
representable range. -/
theorem h3_datagram_frames (d : HttpDatagram) (qb : Bytes)
    (hq : Varint.encVarint d.qsid = some qb) :
    encHttpDatagram d = some (qb ++ d.payload) := by
  simp only [encHttpDatagram, hq]

/-- The *flow id* of a datagram: its Quarter Stream ID (RFC 9297 §2.1). -/
def HttpDatagram.flowId (d : HttpDatagram) : Nat := d.qsid

/-- **Flow-id ↔ request stream.** The datagram's flow id (Quarter Stream ID)
designates the associated request stream `4 · flowId`; that stream is a
client-initiated bidirectional stream (`≡ 0 mod 4`); and the mapping is
invertible — the request stream's id divided by four recovers the flow id. -/
theorem h3_datagram_flow_id (d : HttpDatagram) :
    d.streamId = 4 * d.flowId
      ∧ d.streamId % 4 = 0
      ∧ qsidOfStreamId d.streamId = d.flowId := by
  unfold HttpDatagram.streamId HttpDatagram.flowId streamIdOfQsid qsidOfStreamId
  refine ⟨rfl, by omega, by omega⟩

/-! ## Delivery semantics: unreliability (RFC 9221 §5, surfaced by RFC 9297)

QUIC DATAGRAM frames — and therefore the HTTP/3 datagrams they carry — are an
*unreliable* datagram service: a datagram that is lost is **not** retransmitted,
and datagrams carry **no ordering guarantee**. We model a delivery as: drop an
arbitrary sub-multiset of the sent datagrams (loss / no-retransmission), then
reorder what survives (no ordering). Formally, the received sequence is a
permutation of some sublist of the sent sequence. -/

/-- `Delivers sent received`: `received` is obtainable from `sent` by dropping
some datagrams (loss) and reordering the rest (no ordering guarantee). -/
def Delivers (sent received : List HttpDatagram) : Prop :=
  ∃ mid, mid.Sublist sent ∧ received.Perm mid

/-- **Unreliability semantic.** The delivery relation captures exactly the
RFC 9221 §5 guarantees, and no more:

1. **No retransmission** — total loss is a permitted outcome for any send.
2. **No ordering guarantee** — any reordering of the sent datagrams is a
   permitted delivery.
3. **Integrity** — a delivered datagram was actually sent (nothing is
   fabricated by the transport).
4. **Genuinely weaker than a reliable ordered channel** — some delivery
   differs from the sent sequence, so a receiver may not assume
   `received = sent` (witnessed by loss). -/
theorem h3_datagram_unreliable :
    (∀ sent, Delivers sent []) ∧
    (∀ sent received, received.Perm sent → Delivers sent received) ∧
    (∀ sent received d, Delivers sent received → d ∈ received → d ∈ sent) ∧
    (∃ sent received, Delivers sent received ∧ received ≠ sent) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun sent => ⟨[], List.nil_sublist sent, List.Perm.refl []⟩
  · exact fun sent received hp => ⟨sent, List.Sublist.refl sent, hp⟩
  · rintro sent received d ⟨mid, hsub, hperm⟩ hmem
    exact hsub.subset (hperm.mem_iff.mp hmem)
  · exact ⟨[{ qsid := 0, payload := [] }], [],
      ⟨[], List.nil_sublist _, List.Perm.refl []⟩, by decide⟩

/-! ## Wire vectors, checker-verified -/

-- qsid 4 (→ request stream ID 16) with a 3-byte payload frames and deframes.
#guard encHttpDatagram { qsid := 4, payload := [0xaa, 0xbb, 0xcc] }
    = some [0x04, 0xaa, 0xbb, 0xcc]
#guard decHttpDatagram [0x04, 0xaa, 0xbb, 0xcc]
    = some { qsid := 4, payload := [0xaa, 0xbb, 0xcc] }
-- request stream ID recovered from a decoded datagram: 4 * 4 = 16.
#guard (decHttpDatagram [0x04, 0xaa, 0xbb, 0xcc]).map HttpDatagram.streamId
    = some 16
-- a two-byte qsid (0x4021 → 16417) still round-trips.
#guard decHttpDatagram [0x40, 0x21, 0xde]
    = some { qsid := 0x21, payload := [0xde] }
-- QUIC DATAGRAM frame body (type 0x31): length 4, then the H3 datagram.
#guard encH3OverQuic { qsid := 0, payload := [0x11, 0x22] }
    = some [0x03, 0x00, 0x11, 0x22]
#guard decH3OverQuic [0x03, 0x00, 0x11, 0x22]
    = some { qsid := 0, payload := [0x11, 0x22] }
-- type 0x30: whole remainder is the payload.
#guard decQuicDatagram dgramTypeNoLen [0x00, 0x11, 0x22]
    = some ([0x00, 0x11, 0x22], 3)

#print axioms h3_datagram_encode_decode
#print axioms datagram_qsid_maps
#print axioms decoded_datagram_stream_id
#print axioms h3_over_quic_roundtrip
#print axioms H3.Datagram.h3_datagram_frames
#print axioms H3.Datagram.h3_datagram_flow_id
#print axioms H3.Datagram.h3_datagram_unreliable

end Datagram
end H3
