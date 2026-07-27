import H3.Frame

/-!
# HTTP Extensible Priorities (RFC 9218)

RFC 9218 replaces the deprecated RFC 7540 §5.3 priority tree with a small
signalling scheme shared by HTTP/2 and HTTP/3. Two parameters govern a
response's scheduling:

* **urgency** `u` — an integer in `0..7`, default `3`; lower is more urgent.
* **incremental** `i` — a boolean, default `false`; when set the resource
  benefits from interleaved delivery.

They travel two ways: in the `priority` request/response header field, and in
the **PRIORITY_UPDATE** frame (RFC 9218 §7.1) a client sends on the HTTP/3
control stream to re-prioritize an in-flight request or push. Both carry the
*Priority Field Value* — a Structured Fields (RFC 8941) Dictionary whose only
recognized members are `u` and `i`; unknown members are ignored (§4).

This module models:

* `Prio` — the (urgency, incremental) pair, with `Prio.mk'` clamping urgency
  into `0..7` (§4: values outside the range are invalid and clamped).
* `encodeFieldValue` / `parseFieldValue` — a byte-exact codec for the field
  value in the canonical (minimal) form the reference emits, with a tolerant
  parser (unknown members and reversed order accepted). The headline is
  `parse_encode` — **round-trip** over the whole `0..7 × Bool` domain.
* `higherThan` — the §4/§10 scheduling order (urgency first, then
  non-incremental before incremental at equal urgency), proven a strict order.
* `PriorityUpdate` + `encPriorityUpdate` / `decPriorityUpdate` — the
  PRIORITY_UPDATE request (type `0x0F0700`) and push (type `0x0F0701`) frames
  (RFC 9218 §7.1), with a **round-trip** theorem built on the proven QUIC
  varint codec of `H3.Varint`.

Byte strings are `List UInt8` throughout, matching the rest of the package.
-/

namespace H3
namespace Priority

open H3 (Bytes)

/-- Default urgency (RFC 9218 §4). -/
def defaultUrgency : Nat := 3

/-- Maximum urgency = lowest priority (RFC 9218 §4). -/
def maxUrgency : Nat := 7

/-- The Priority Field Value parameters (RFC 9218 §4). -/
structure Prio where
  urgency : Nat
  incremental : Bool
deriving Repr, DecidableEq

/-- The RFC 9218 defaults: `u=3`, `i=false`. -/
def Prio.default : Prio := ⟨defaultUrgency, false⟩

/-- Clamping constructor (RFC 9218 §4: urgency outside `0..7` is clamped). -/
def Prio.mk' (u : Nat) (i : Bool) : Prio := ⟨min u maxUrgency, i⟩

theorem Prio.mk'_urgency_le (u : Nat) (i : Bool) :
    (Prio.mk' u i).urgency ≤ maxUrgency := by
  simp [Prio.mk', maxUrgency]; omega

/-! ## ASCII helpers -/

def chU : UInt8 := 0x75    -- 'u'
def chI : UInt8 := 0x69    -- 'i'
def chEq : UInt8 := 0x3d   -- '='
def chComma : UInt8 := 0x2c -- ','
def chSpace : UInt8 := 0x20 -- ' '

/-- ASCII digit byte for `d < 10`. -/
def digit (d : Nat) : UInt8 := UInt8.ofNat (0x30 + d)

/-- Parse a single ASCII digit byte to its value, or `none`. -/
def unDigit (b : UInt8) : Option Nat :=
  if 0x30 ≤ b.toNat ∧ b.toNat ≤ 0x39 then some (b.toNat - 0x30) else none

/-! ## The Priority Field Value codec (RFC 9218 §4) -/

/-- Encode a priority to its canonical (minimal) Structured-Fields form, as
the reference does: only members differing from their defaults are emitted.

* both default → empty
* `u≠3`, `i=false` → `u=D`
* `u=3`, `i=true`  → `i`
* `u≠3`, `i=true`  → `u=D, i`

Urgency is emitted as a single digit; callers should pass a clamped `Prio`
(`Prio.mk'`), the only case the codec is specified for. -/
def encodeFieldValue (p : Prio) : Bytes :=
  let uDefault : Bool := p.urgency == defaultUrgency
  let uPart : Bytes := if uDefault then [] else [chU, chEq, digit p.urgency]
  match uDefault, p.incremental with
  | true, false => []
  | true, true => [chI]
  | false, false => uPart
  | false, true => uPart ++ [chComma, chSpace, chI]

/-- Drop leading spaces. -/
def dropSpaces : Bytes → Bytes
  | [] => []
  | b :: rest => if b = chSpace then dropSpaces rest else b :: rest

/-- Trim trailing spaces. -/
def dropTrailingSpaces (bs : Bytes) : Bytes :=
  (dropSpaces bs.reverse).reverse

/-- Trim leading and trailing spaces. -/
def trim (bs : Bytes) : Bytes := dropTrailingSpaces (dropSpaces bs)

/-- Split a byte string on commas. -/
def splitComma : Bytes → List Bytes
  | [] => [[]]
  | b :: rest =>
    if b = chComma then [] :: splitComma rest
    else match splitComma rest with
      | [] => [[b]]
      | tok :: toks => (b :: tok) :: toks

/-- Apply one dictionary member (already trimmed) to the accumulator.
Recognizes `u=D` (single digit, clamped) and the bare `i` boolean; every
other token — unknown members, malformed urgency — is ignored (§4). -/
def parseToken (p : Prio) (tok : Bytes) : Prio :=
  match tok with
  | [] => p
  | [b] => if b = chI then { p with incremental := true } else p
  | [a, b, c] =>
    if a = chU ∧ b = chEq then
      match unDigit c with
      | some d => { p with urgency := min d maxUrgency }
      | none => p
    else p
  | _ => p

/-- Parse a Priority Field Value: split on commas, trim, fold each member
into the defaults. Tolerant of unknown members and member order (§4). -/
def parseFieldValue (bs : Bytes) : Prio :=
  (splitComma bs).foldl (fun p tok => parseToken p (trim tok)) Prio.default

/-! ## Round-trip -/

theorem unDigit_digit (d : Nat) (h : d ≤ 9) : unDigit (digit d) = some d := by
  have : (digit d).toNat = 0x30 + d := by
    show (0x30 + d) % 256 = 0x30 + d
    omega
  simp [unDigit, this]; omega

/-- **Round-trip.** For every urgency in `0..7` and every incremental flag,
parsing the canonical encoding recovers the priority exactly. Ranging over
the whole valid domain, so non-vacuous. -/
theorem parse_encode (u : Nat) (hu : u ≤ maxUrgency) (i : Bool) :
    parseFieldValue (encodeFieldValue ⟨u, i⟩) = ⟨u, i⟩ := by
  simp only [maxUrgency] at hu
  rcases u with _|_|_|_|_|_|_|_|u
  · cases i <;> rfl
  · cases i <;> rfl
  · cases i <;> rfl
  · cases i <;> rfl
  · cases i <;> rfl
  · cases i <;> rfl
  · cases i <;> rfl
  · cases i <;> rfl
  · exact absurd hu (by omega)

/-- The clamped form round-trips for arbitrary urgency input. -/
theorem parse_encode_mk' (u : Nat) (i : Bool) :
    parseFieldValue (encodeFieldValue (Prio.mk' u i)) = Prio.mk' u i :=
  parse_encode _ (Prio.mk'_urgency_le u i) i

/-! ## Scheduling order (RFC 9218 §4, §10) -/

/-- Should `a` be scheduled before `b`? Lower urgency wins; at equal urgency
a non-incremental response precedes an incremental one (§10). -/
def higherThan (a b : Prio) : Bool :=
  if a.urgency ≠ b.urgency then decide (a.urgency < b.urgency)
  else (!a.incremental && b.incremental)

/-- Irreflexive: nothing outranks itself. -/
theorem higherThan_irrefl (a : Prio) : higherThan a a = false := by
  simp [higherThan]

/-- Asymmetric: at most one direction can outrank. -/
theorem higherThan_asymm (a b : Prio) (h : higherThan a b = true) :
    higherThan b a = false := by
  unfold higherThan at h ⊢
  by_cases hu : a.urgency = b.urgency
  · rw [if_neg (not_not_intro hu)] at h
    rw [if_neg (not_not_intro hu.symm)]
    revert h; cases a.incremental <;> cases b.incremental <;> simp
  · rw [if_pos hu] at h
    rw [if_pos (Ne.symm hu)]
    simp only [decide_eq_true_eq] at h
    simp only [decide_eq_false_iff_not]
    omega

/-- Urgency governs: strictly lower urgency is strictly higher priority. -/
theorem higherThan_of_urgency (a b : Prio) (h : a.urgency < b.urgency) :
    higherThan a b = true := by
  have hne : a.urgency ≠ b.urgency := by omega
  unfold higherThan
  rw [if_pos hne]
  simp only [decide_eq_true_eq]; omega

/-- Transitive — a genuine strict order. -/
theorem higherThan_trans (a b c : Prio)
    (hab : higherThan a b = true) (hbc : higherThan b c = true) :
    higherThan a c = true := by
  unfold higherThan at hab hbc ⊢
  by_cases h1 : a.urgency = b.urgency <;> by_cases h2 : b.urgency = c.urgency
  · rw [if_neg (not_not_intro h1)] at hab
    rw [if_neg (not_not_intro h2)] at hbc
    rw [if_neg (not_not_intro (h1.trans h2))]
    revert hab hbc
    cases a.incremental <;> cases b.incremental <;> cases c.incremental <;> simp
  · rw [if_neg (not_not_intro h1)] at hab
    rw [if_pos h2] at hbc
    rw [if_pos (h1 ▸ h2)]
    simp only [decide_eq_true_eq] at hbc ⊢; omega
  · rw [if_pos h1] at hab
    rw [if_neg (not_not_intro h2)] at hbc
    rw [if_pos (h2 ▸ h1)]
    simp only [decide_eq_true_eq] at hab ⊢; omega
  · rw [if_pos h1] at hab
    rw [if_pos h2] at hbc
    have hac : a.urgency ≠ c.urgency := by
      simp only [decide_eq_true_eq] at hab hbc; omega
    rw [if_pos hac]
    simp only [decide_eq_true_eq] at *; omega

/-! ## PRIORITY_UPDATE frames (RFC 9218 §7.1) -/

/-- Frame type for a PRIORITY_UPDATE addressing a request stream. -/
def typeRequest : Nat := 0x0F0700

/-- Frame type for a PRIORITY_UPDATE addressing a push stream. -/
def typePush : Nat := 0x0F0701

/-- A PRIORITY_UPDATE frame: the prioritized element id (a stream id for a
request, a push id for a push) plus the raw Priority Field Value. -/
inductive PriorityUpdate where
  | request (streamId : Nat) (fieldValue : Bytes)
  | push (pushId : Nat) (fieldValue : Bytes)
deriving Repr, DecidableEq

/-- The prioritized element id of a PRIORITY_UPDATE. -/
def PriorityUpdate.elementId : PriorityUpdate → Nat
  | .request s _ => s
  | .push p _ => p

/-- The field value bytes of a PRIORITY_UPDATE. -/
def PriorityUpdate.fieldValue : PriorityUpdate → Bytes
  | .request _ v => v
  | .push _ v => v

/-- Encode a PRIORITY_UPDATE to wire bytes: `[type][length][id][field value]`.
`none` iff the element id exceeds the varint range. -/
def encPriorityUpdate (pu : PriorityUpdate) : Option Bytes :=
  let (ty, id, fv) := match pu with
    | .request s v => (typeRequest, s, v)
    | .push p v => (typePush, p, v)
  match Varint.encVarint id with
  | none => none
  | some idb =>
    let payload := idb ++ fv
    match Varint.encVarint ty, Varint.encVarint payload.length with
    | some tb, some lb => some (tb ++ (lb ++ payload))
    | _, _ => none

/-- Decode a PRIORITY_UPDATE from the head of `bs`. Returns the frame and the
number of bytes consumed. `none` on a truncated header/payload or an
unrecognized type. -/
def decPriorityUpdate (bs : Bytes) : Option (PriorityUpdate × Nat) :=
  match Varint.decVarint bs with
  | none => none
  | some (ty, n1) =>
    match Varint.decVarint (bs.drop n1) with
    | none => none
    | some (len, n2) =>
      let body := bs.drop (n1 + n2)
      if body.length < len then none
      else
        let payload := body.take len
        match Varint.decVarint payload with
        | none => none
        | some (id, m) =>
          let fv := payload.drop m
          if ty = typeRequest then some (.request id fv, n1 + n2 + len)
          else if ty = typePush then some (.push id fv, n1 + n2 + len)
          else none

/-- **PRIORITY_UPDATE round-trip.** Every encodable PRIORITY_UPDATE decodes
back to itself and reports the full encoded length. Built on the proven QUIC
varint round-trip. -/
theorem decPriorityUpdate_encPriorityUpdate (pu : PriorityUpdate) (bs : Bytes)
    (h : encPriorityUpdate pu = some bs) :
    decPriorityUpdate bs = some (pu, bs.length) := by
  -- Uniformly name the type/id/field-value triple for both constructors; the
  -- only per-constructor difference is which `if` branch of the decoder fires.
  have key : ∀ (ty id : Nat) (fv : Bytes) (out : PriorityUpdate),
      (ty = typeRequest ∧ out = .request id fv) ∨
      (ty = typePush ∧ out = .push id fv) →
      (match Varint.encVarint id with
        | none => none
        | some idb =>
          let payload := idb ++ fv
          match Varint.encVarint ty, Varint.encVarint payload.length with
          | some tb, some lb => some (tb ++ (lb ++ payload))
          | _, _ => none) = some bs →
      decPriorityUpdate bs = some (out, bs.length) := by
    intro ty id fv out hout henc
    cases hidb : Varint.encVarint id with
    | none => rw [hidb] at henc; simp at henc
    | some idb =>
      rw [hidb] at henc
      simp only [] at henc
      cases htb : Varint.encVarint ty with
      | none => rw [htb] at henc; simp at henc
      | some tb =>
        cases hlb : Varint.encVarint (idb ++ fv).length with
        | none => rw [htb, hlb] at henc; simp at henc
        | some lb =>
          rw [htb, hlb] at henc
          simp only [Option.some.injEq] at henc
          subst henc
          -- Decode: type, length, then id, then field value. Everything is
          -- right-associated to match `decVarint_encVarint`'s `bs ++ tail`.
          unfold decPriorityUpdate
          rw [Varint.decVarint_encVarint ty tb (lb ++ (idb ++ fv)) htb]
          dsimp only
          rw [List.drop_left]
          rw [Varint.decVarint_encVarint (idb ++ fv).length lb (idb ++ fv) hlb]
          dsimp only
          have hdrop2 : (tb ++ (lb ++ (idb ++ fv))).drop (tb.length + lb.length)
              = idb ++ fv := by
            rw [show tb ++ (lb ++ (idb ++ fv)) = (tb ++ lb) ++ (idb ++ fv) by
                  simp [List.append_assoc],
                show tb.length + lb.length = (tb ++ lb).length by simp]
            exact List.drop_left
          rw [hdrop2, if_neg (by simp), List.take_length,
            Varint.decVarint_encVarint id idb fv hidb]
          dsimp only
          rw [List.drop_left]
          have hbslen : (tb ++ (lb ++ (idb ++ fv))).length
              = tb.length + lb.length + (idb ++ fv).length := by
            simp [List.length_append]; omega
          rcases hout with ⟨hteq, hmk⟩ | ⟨hteq, hmk⟩
          · rw [if_pos hteq, hmk, hbslen]
          · rw [if_neg (by rw [hteq]; decide), if_pos hteq, hmk, hbslen]
  unfold encPriorityUpdate at h
  cases pu with
  | request s v =>
    exact key typeRequest s v (.request s v) (Or.inl ⟨rfl, rfl⟩) h
  | push p v =>
    exact key typePush p v (.push p v) (Or.inr ⟨rfl, rfl⟩) h

/-! ## Wire vectors and tolerance, checker-verified -/

-- Canonical field-value encodings.
#guard encodeFieldValue ⟨3, false⟩ = []
#guard encodeFieldValue ⟨1, false⟩ = [chU, chEq, 0x31]       -- "u=1"
#guard encodeFieldValue ⟨3, true⟩ = [chI]                     -- "i"
#guard encodeFieldValue ⟨0, true⟩ = [chU, chEq, 0x30, chComma, chSpace, chI] -- "u=0, i"

-- Tolerant parse: unknown members and reversed order (RFC 9218 §4).
-- "u=2, i, x=42"  →  u=2, i=true
#guard parseFieldValue [chU, chEq, 0x32, chComma, chSpace, chI, chComma,
  chSpace, 0x78, chEq, 0x34, 0x32] = ⟨2, true⟩
-- "i, u=5"  →  u=5, i=true  (order-independent)
#guard parseFieldValue [chI, chComma, chSpace, chU, chEq, 0x35] = ⟨5, true⟩
-- out-of-range urgency clamps: "u=9" → u=7
#guard parseFieldValue [chU, chEq, 0x39] = ⟨maxUrgency, false⟩
-- empty value → defaults
#guard parseFieldValue [] = Prio.default

-- Scheduling order sanity (non-vacuous witnesses).
#guard higherThan ⟨0, false⟩ ⟨7, false⟩ = true
#guard higherThan ⟨7, false⟩ ⟨0, false⟩ = false
#guard higherThan ⟨3, false⟩ ⟨3, true⟩ = true   -- non-incremental first
#guard higherThan ⟨3, false⟩ ⟨3, false⟩ = false -- irreflexive

-- PRIORITY_UPDATE round-trip execution vectors.
private def vecPuRequest : Bool :=
  match encPriorityUpdate (.request 4 (encodeFieldValue ⟨1, true⟩)) with
  | some bs =>
    decPriorityUpdate bs == some (.request 4 (encodeFieldValue ⟨1, true⟩), bs.length)
  | none => false
#guard vecPuRequest

private def vecPuPush : Bool :=
  match encPriorityUpdate (.push 8 (encodeFieldValue ⟨5, false⟩)) with
  | some bs =>
    decPriorityUpdate bs == some (.push 8 (encodeFieldValue ⟨5, false⟩), bs.length)
  | none => false
#guard vecPuPush

#print axioms parse_encode
#print axioms decPriorityUpdate_encPriorityUpdate

end Priority
end H3
