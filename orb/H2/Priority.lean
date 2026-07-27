import H2.Frame

/-!
# HTTP/2 stream priority (RFC 7540 §5.3, §6.3)

The **PRIORITY** frame (type `0x2`) carries a stream's priority signal: a
32-bit dependency word (the high `E` bit is *exclusive*, the low 31 bits are the
**stream dependency**) followed by a one-octet **weight** (RFC 7540 §6.3):

```text
+-+-------------------------------------------------------------+
|E|                  Stream Dependency (31)                     |
+-+-------------+-----------------------------------------------+
|   Weight (8)  |
+-+-------------+
```

The wire weight octet `W` denotes an effective weight of `W + 1`, in the range
`1..256` (RFC 7540 §6.3), so the wire octet `15` is the default weight `16`.

This module sits on top of the frame layer (`H2/Frame.lean`): `H2.decode`
recognises a PRIORITY frame and hands the raw 5-octet payload to `parsePriority`
here; `validate` then applies the two structural checks the RFC mandates before
a priority signal may be accepted:

* **length** — a PRIORITY frame whose payload is not exactly 5 octets is a
  `FRAME_SIZE_ERROR` (RFC 7540 §6.3) — `parsePriority` is `none` off length 5,
  and `validate` reports `frameSizeError`.
* **stream 0** — a PRIORITY frame on stream `0x0` is a connection
  `PROTOCOL_ERROR` (RFC 7540 §6.3).
* **self-dependency** — a stream may not depend on itself; a dependency equal to
  the frame's own stream id is a `PROTOCOL_ERROR` (RFC 7540 §5.3.1) —
  `h2_priority_no_self_dep`.

Headline results:

* `h2_priority_frame` — every 5-octet payload parses to a well-formed signal: a
  31-bit dependency, an effective weight in `1..256`, and the `E` bit read off
  the top of the dependency word.
* `h2_priority_no_self_dep` — a stream depending on itself is rejected with
  `PROTOCOL_ERROR`.
* `h2_priority_default` — the absent-priority default is weight `16`,
  dependency `0`, non-exclusive (RFC 7540 §5.3.5), and it is exactly what the
  canonical zero-dependency / `15` weight octet decodes to.

The RFC 9113 (2022) revision deprecates the priority *scheme* (the dependency
tree is no longer used for scheduling) but PRIORITY frames must still parse and
the structural error checks still apply, which is exactly what is modelled here.
-/

namespace H2
namespace Priority

/-- A parsed PRIORITY signal. `weight` is the **effective** weight (`1..256`),
already incremented off the wire octet (RFC 7540 §6.3). -/
structure PriorityFields where
  /-- The `E` (exclusive) bit — the top bit of the dependency word. -/
  exclusive : Bool
  /-- The 31-bit stream dependency. -/
  dependency : Nat
  /-- The effective weight, `1..256` (wire octet `+ 1`). -/
  weight : Nat
deriving Repr, DecidableEq

/-- Outcome of accepting a PRIORITY frame. `frameSizeError` is RFC 7540's
FRAME_SIZE_ERROR (payload length ≠ 5); `protocolError` covers the stream-0 and
self-dependency rules. -/
inductive PriorityResult where
  | ok (p : PriorityFields)
  | frameSizeError
  | protocolError
deriving Repr, DecidableEq

/-- The default stream weight (RFC 7540 §5.3.5). -/
def defaultWeight : Nat := 16

/-- The default stream dependency: every stream initially depends on stream 0,
non-exclusively (RFC 7540 §5.3.5). -/
def defaultDependency : Nat := 0

/-- The priority signal of a stream with no PRIORITY frame (RFC 7540 §5.3.5):
non-exclusive dependency on stream 0 with weight 16. -/
def defaultPriority : PriorityFields :=
  { exclusive := false, dependency := defaultDependency, weight := defaultWeight }

/-- Parse the 5-octet PRIORITY payload (RFC 7540 §6.3). Any other length is
`none` (the caller raises FRAME_SIZE_ERROR). The dependency word is big-endian;
the `E` bit is bit 31, the dependency the low 31 bits, and the weight octet is
incremented to its effective `1..256` value. -/
def parsePriority : Bytes → Option PriorityFields
  | [p0, p1, p2, p3, p4] =>
    let depWord := p0.toNat * 2 ^ 24 + p1.toNat * 2 ^ 16 + p2.toNat * 2 ^ 8 + p3.toNat
    some { exclusive := decide (depWord / 2 ^ 31 = 1)
           dependency := depWord % 2 ^ 31
           weight := p4.toNat + 1 }
  | _ => none

/-- Accept a PRIORITY frame received on stream `streamId` with raw `payload`
(RFC 7540 §6.3, §5.3.1): length check, then the stream-0 and self-dependency
protocol checks, then a well-formed signal. -/
def validate (streamId : Nat) (payload : Bytes) : PriorityResult :=
  match parsePriority payload with
  | none => .frameSizeError
  | some p =>
    if streamId = 0 then .protocolError
    else if p.dependency = streamId then .protocolError
    else .ok p

/-! ## `h2_priority_frame` — a PRIORITY payload parses to a dependency + weight -/

/-- **PRIORITY parse well-formedness** (RFC 7540 §6.3): every 5-octet payload
parses to a signal whose dependency is a 31-bit value, whose effective weight is
in `1..256`, and whose `E` bit is the top bit of the big-endian dependency
word. -/
theorem h2_priority_frame (p0 p1 p2 p3 p4 : UInt8) :
    ∃ p, parsePriority [p0, p1, p2, p3, p4] = some p ∧
      p.dependency < 2 ^ 31 ∧ 1 ≤ p.weight ∧ p.weight ≤ 256 ∧
      p.exclusive =
        decide ((p0.toNat * 2 ^ 24 + p1.toNat * 2 ^ 16 + p2.toNat * 2 ^ 8 + p3.toNat)
                  / 2 ^ 31 = 1) := by
  refine ⟨_, rfl, ?_, ?_, ?_, rfl⟩
  · exact Nat.mod_lt _ (by decide)
  · exact Nat.le_add_left 1 p4.toNat
  · show p4.toNat + 1 ≤ 256
    have := u8_toNat_lt p4
    omega

/-- The parsed dependency never occupies the reserved `E` bit — it is a 31-bit
field, disjoint from the exclusivity flag (RFC 7540 §6.3). -/
theorem parsePriority_dependency_lt (p0 p1 p2 p3 p4 : UInt8) (p : PriorityFields)
    (h : parsePriority [p0, p1, p2, p3, p4] = some p) : p.dependency < 2 ^ 31 := by
  simp only [parsePriority, Option.some.injEq] at h
  subst h
  exact Nat.mod_lt _ (by decide)

/-! ## `h2_priority_no_self_dep` — self-dependency is PROTOCOL_ERROR -/

/-- **Self-dependency rejection** (RFC 7540 §5.3.1): a stream may not depend on
itself. A PRIORITY frame on a non-zero stream whose parsed dependency equals its
own stream id is rejected with `PROTOCOL_ERROR`. -/
theorem h2_priority_no_self_dep (streamId : Nat) (payload : Bytes) (p : PriorityFields)
    (hparse : parsePriority payload = some p) (hnz : streamId ≠ 0)
    (hself : p.dependency = streamId) :
    validate streamId payload = .protocolError := by
  simp only [validate, hparse]
  rw [if_neg hnz, if_pos hself]

/-- Witness that `h2_priority_no_self_dep`'s hypotheses are inhabited (so the
theorem is not vacuous): stream 3 with a dependency of 3 is a concrete rejection.
Dependency word `0x0000_0003`, weight octet `0`. -/
example : validate 3 [0x00, 0x00, 0x00, 0x03, 0x00] = .protocolError := by decide

/-- A PRIORITY frame on stream 0 is a `PROTOCOL_ERROR` regardless of payload
contents (RFC 7540 §6.3). -/
theorem h2_priority_stream0 (payload : Bytes) (p : PriorityFields)
    (hparse : parsePriority payload = some p) :
    validate 0 payload = .protocolError := by
  simp [validate, hparse]

/-- A non-self, non-zero-stream PRIORITY frame is accepted with its signal — the
error checks do not over-reject (converse to `h2_priority_no_self_dep`). -/
theorem validate_ok (streamId : Nat) (payload : Bytes) (p : PriorityFields)
    (hparse : parsePriority payload = some p) (hnz : streamId ≠ 0)
    (hne : p.dependency ≠ streamId) :
    validate streamId payload = .ok p := by
  simp only [validate, hparse]
  rw [if_neg hnz, if_neg hne]

/-- A PRIORITY payload of any length other than 5 is a FRAME_SIZE_ERROR
(RFC 7540 §6.3). -/
theorem h2_priority_frame_size (streamId : Nat) (payload : Bytes)
    (h : payload.length ≠ 5) : validate streamId payload = .frameSizeError := by
  have hp : parsePriority payload = none := by
    rcases payload with _|⟨a,_|⟨b,_|⟨c,_|⟨d,_|⟨e,_|⟨f,rest⟩⟩⟩⟩⟩⟩ <;>
      simp_all [parsePriority]
  simp only [validate, hp]

/-! ## `h2_priority_default` — the absent-priority default -/

/-- **Absent-priority default** (RFC 7540 §5.3.5): a stream with no PRIORITY
frame has weight 16, dependency 0, and is non-exclusive; and that default is
exactly what the canonical wire form (zero dependency word, weight octet `15`)
decodes to. -/
theorem h2_priority_default :
    defaultPriority.weight = 16 ∧ defaultPriority.dependency = 0 ∧
      defaultPriority.exclusive = false ∧
      parsePriority [0x00, 0x00, 0x00, 0x00, 0x0f] = some defaultPriority :=
  ⟨rfl, rfl, rfl, by decide⟩

/-! ## Wire vectors, checker-verified -/

/-- Exclusive dependency on stream 1, effective weight 129: dependency word
`0x8000_0001`, weight octet `0x80`. -/
example : parsePriority [0x80, 0x00, 0x00, 0x01, 0x80]
    = some { exclusive := true, dependency := 1, weight := 129 } := by decide

/-- Non-exclusive dependency on stream `0x0091_A2B3`, effective weight 256
(wire octet `0xFF`). -/
example : parsePriority [0x00, 0x91, 0xA2, 0xB3, 0xFF]
    = some { exclusive := false, dependency := 0x0091A2B3, weight := 256 } := by decide

/-- A 4-octet payload (truncated dependency word) is FRAME_SIZE_ERROR. -/
example : validate 5 [0x00, 0x00, 0x00, 0x01] = .frameSizeError := by decide

/-- End-to-end through the frame layer: a PRIORITY frame (type `0x2`) on stream
3, exclusive dependency on stream 1, weight octet `0x80`, decodes via
`H2.decode` and then `validate`s to an accepted signal (dep 1 ≠ stream 3). -/
example :
    (match H2.decode [0x00, 0x00, 0x05, 0x02, 0x00, 0x00, 0x00, 0x00, 0x03,
                      0x80, 0x00, 0x00, 0x01, 0x80] 16384 with
     | .complete (.priority sid pl) _ => validate sid pl
     | _ => .frameSizeError)
      = .ok { exclusive := true, dependency := 1, weight := 129 } := by decide

/-- End-to-end self-dependency: a PRIORITY frame on stream 3 whose dependency is
also 3 decodes at the frame layer and then `validate`s to `PROTOCOL_ERROR`. -/
example :
    (match H2.decode [0x00, 0x00, 0x05, 0x02, 0x00, 0x00, 0x00, 0x00, 0x03,
                      0x00, 0x00, 0x00, 0x03, 0x0a] 16384 with
     | .complete (.priority sid pl) _ => validate sid pl
     | _ => .frameSizeError)
      = .protocolError := by decide

end Priority
end H2
