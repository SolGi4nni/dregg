import Dns.EncodeRData

/-!
# SVCB / HTTPS resource records (RFC 9460)

The `SVCB` (type 64) and `HTTPS` (type 65) resource records share one wire
shape (RFC 9460 §2.2):

```
  SvcPriority (16)  TargetName (domain name)  SvcParams (TLV list)
```

`Dns.typedRData` already reads this shape for both type codes and
`Dns.encodeRData` writes it; this module closes the row with the three
load-bearing facts an SVCB/HTTPS implementation must guarantee:

* **`svcb_encode_decode`** — the composed record round-trips: a priority, a
  target name, and a SvcParams TLV list written by `encodeRData` parse back to
  exactly the value written, with the RDATA embedded at any offset of any
  message (names inside SVCB RDATA are position-dependent, so the statement is
  embedded, like MX). The SvcParams cover the five registered keys an HTTPS
  record uses in practice — `alpn` (1), `port` (3), `ipv4hint` (4), `ech` (5),
  `ipv6hint` (6).

* **`https_record_is_svcb`** — the HTTPS RR (type 65) is decoded through the
  very same SVCB (type 64) wire format: for any message and record body, the
  two type codes yield identical typed RDATA. HTTPS is SVCB with a different
  type number, and the reader proves it.

* **`svcparams_sorted`** — RFC 9460 §2.2 requires SvcParams to appear in
  strictly increasing key order. `keysAscending` is that order predicate, and
  the theorem shows a real HTTPS record whose SvcParams are ascending decodes
  off the wire to a SvcParams list that is *still* ascending — order is a wire
  invariant of the round-trip.

All three are discharged for a concrete real HTTPS record at the end, so none
of the hypotheses is vacuous.
-/

namespace Dns

/-! ## The SVCB / HTTPS round-trip -/

/-- **The SVCB/HTTPS record round-trip (RFC 9460 §2.2).** The SvcPriority,
TargetName and SvcParams written by `encodeRData` parse back verbatim through
the deployed `typedRData` reader for type 65 (HTTPS). Stated embedded: the
RDATA sits at offset `pre.length` of the message `pre ++ (rdata ++ rest)`, so
the target name (which `typedRData` decodes against the whole message at the
RDATA offset) resolves at its true position. Side conditions are exactly the
RFC field widths: priority 16-bit, target a legal name, each SvcParam key and
value length 16-bit. -/
theorem svcb_encode_decode (pre rest : Bytes) (nm target : List (List UInt8))
    (cls ttl priority : Nat) (params : List (Nat × List UInt8))
    (hpri : priority < 65536) (hok : LabelsOk target) (hcap : wireLen target ≤ maxName)
    (hparams : ∀ p ∈ params, p.1 < 65536 ∧ p.2.length < 65536) :
    typedRData (pre ++ (encodeRData (.svcb priority target params) ++ rest))
      ⟨{ name := nm, rrType := 65, rrClass := cls, ttl := ttl,
         rdata := encodeRData (.svcb priority target params) }, pre.length⟩
      = some (.svcb priority target params) := by
  -- the reader's type-65 branch, in terms of the encoded RDATA
  have hbranch : typedRData (pre ++ (encodeRData (.svcb priority target params) ++ rest))
      ⟨{ name := nm, rrType := 65, rrClass := cls, ttl := ttl,
         rdata := encodeRData (.svcb priority target params) }, pre.length⟩
      = if 2 ≤ (encodeRData (.svcb priority target params)).length then
          match decodeName (pre ++ (encodeRData (.svcb priority target params) ++ rest))
              (pre.length + 2) with
          | .error _ => none
          | .ok t =>
            match tlvs ((encodeRData (.svcb priority target params)).drop (2 + t.consumed)) with
            | none => none
            | some ps =>
              some (.svcb (be16At (encodeRData (.svcb priority target params)) 0) t.labels ps)
        else none := rfl
  -- the RDATA is at least the 2 priority octets long
  have hlen2 : 2 ≤ (encodeRData (.svcb priority target params)).length := by
    show 2 ≤ (putBe 2 priority ++ (encodeName target ++ encodeTlvs params)).length
    rw [List.length_append, putBe_length]; omega
  -- re-associate so the target name starts at offset pre.length + 2
  have hassoc : pre ++ (encodeRData (.svcb priority target params) ++ rest)
      = (pre ++ putBe 2 priority) ++ (encodeName target ++ (encodeTlvs params ++ rest)) := by
    show pre ++ ((putBe 2 priority ++ (encodeName target ++ encodeTlvs params)) ++ rest) = _
    simp [List.append_assoc]
  have hofflen : pre.length + 2 = (pre ++ putBe 2 priority).length := by
    rw [List.length_append, putBe_length]
  have hdec : decodeName (pre ++ (encodeRData (.svcb priority target params) ++ rest))
      (pre.length + 2) = .ok ⟨target, wireLen target⟩ := by
    rw [hassoc, hofflen]
    exact decodeName_encodeName_at (pre ++ putBe 2 priority) (encodeTlvs params ++ rest) target hok hcap
  -- the SvcParams region is exactly what `encodeTlvs` wrote
  have hdrop : (encodeRData (.svcb priority target params)).drop (2 + wireLen target)
      = encodeTlvs params := by
    have e : encodeRData (.svcb priority target params)
        = (putBe 2 priority ++ encodeName target) ++ encodeTlvs params := by
      show putBe 2 priority ++ (encodeName target ++ encodeTlvs params) = _
      rw [List.append_assoc]
    have hl : (putBe 2 priority ++ encodeName target).length = 2 + wireLen target := by
      rw [List.length_append, putBe_length, encodeName_length]
    rw [e, ← hl, List.drop_left]
  -- the priority reads back
  have h16 : be16At (encodeRData (.svcb priority target params)) 0 = priority := by
    have e : encodeRData (.svcb priority target params)
        = UInt8.ofNat (priority / 256) :: UInt8.ofNat priority
            :: (encodeName target ++ encodeTlvs params) := by
      simp [encodeRData, putBe]
    rw [e]
    simp only [be16At, List.getD_cons_zero, List.getD_cons_succ]
    exact be16_putU16 priority hpri
  rw [hbranch, if_pos hlen2, hdec]
  show (match tlvs ((encodeRData (.svcb priority target params)).drop (2 + wireLen target)) with
        | none => none
        | some ps =>
          some (RData.svcb (be16At (encodeRData (.svcb priority target params)) 0) target ps))
      = some (RData.svcb priority target params)
  rw [hdrop, tlvs_encode params hparams, h16]

/-! ## HTTPS is SVCB (RFC 9460 §2/§9) -/

/-- **HTTPS (type 65) is decoded as SVCB (type 64).** For any message, record
body, and RDATA offset, the typed reader gives the same result whether the
record's type is 64 or 65 — the HTTPS RR is the SVCB wire format under a
distinct type number (RFC 9460 §9). The two `typedRData` branches are the same
code, and this makes that a theorem rather than a comment. -/
theorem https_record_is_svcb (msg : Bytes) (rr : RR) (off : Nat) :
    typedRData msg ⟨{ rr with rrType := 65 }, off⟩
      = typedRData msg ⟨{ rr with rrType := 64 }, off⟩ := rfl

/-! ## SvcParams are in strictly increasing key order (RFC 9460 §2.2) -/

/-- Strictly increasing SvcParam key order (RFC 9460 §2.2): each key is smaller
than the next. A single param (or none) is trivially ordered. -/
def keysAscending : List (Nat × List UInt8) → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => a.1 < b.1 ∧ keysAscending (b :: rest)

/-- **SvcParams key order survives the wire (RFC 9460 §2.2).** A real HTTPS
record whose SvcParams are in strictly increasing key order encodes and decodes
back to a SvcParams list that is *still* in strictly increasing key order — the
decoded params are exhibited and shown ascending, so ordering is a genuine
round-trip invariant, not just an encoder-side convention. -/
theorem svcparams_sorted (pre rest : Bytes) (nm target : List (List UInt8))
    (cls ttl priority : Nat) (params : List (Nat × List UInt8))
    (hpri : priority < 65536) (hok : LabelsOk target) (hcap : wireLen target ≤ maxName)
    (hparams : ∀ p ∈ params, p.1 < 65536 ∧ p.2.length < 65536)
    (hsorted : keysAscending params) :
    ∃ ps, typedRData (pre ++ (encodeRData (.svcb priority target params) ++ rest))
            ⟨{ name := nm, rrType := 65, rrClass := cls, ttl := ttl,
               rdata := encodeRData (.svcb priority target params) }, pre.length⟩
          = some (.svcb priority target ps) ∧ keysAscending ps :=
  ⟨params, svcb_encode_decode pre rest nm target cls ttl priority params hpri hok hcap hparams,
    hsorted⟩

/-! ## A concrete real HTTPS record (non-vacuity witness)

`cdn.example.com` HTTPS RR, priority 1, with the five SvcParams an HTTPS record
carries in practice, in ascending key order:
`alpn` (h3, h2), `port` 443, `ipv4hint`, `ech`, `ipv6hint`. -/

/-- Target name `cdn.example.com`. -/
def httpsTarget : List (List UInt8) :=
  [[99, 100, 110], [101, 120, 97, 109, 112, 108, 101], [99, 111, 109]]

/-- The SvcParams of a real HTTPS record, keys strictly ascending (1 < 3 < 4 < 5 < 6). -/
def httpsParams : List (Nat × List UInt8) :=
  [ (1, [2, 104, 51, 2, 104, 50]),        -- alpn: "h3", "h2"
    (3, [0x01, 0xBB]),                      -- port 443
    (4, [104, 16, 132, 229]),               -- ipv4hint 104.16.132.229
    (5, [0xAB, 0xCD]),                      -- ech (opaque ECHConfigList)
    (6, [0x26, 0x06, 0x47, 0x00, 0, 0, 0, 0, 0, 0, 0, 0, 0x68, 0x10, 0x84, 0xE5]) ]  -- ipv6hint

/-- Every label of `httpsTarget` is a legal 1..63-octet label. -/
theorem httpsTarget_ok : LabelsOk httpsTarget := by
  intro lab hlab
  simp only [httpsTarget, List.mem_cons, List.not_mem_nil, or_false] at hlab
  rcases hlab with h | h | h <;> subst h <;> exact ⟨by decide, by decide⟩

/-- The real HTTPS record's SvcParams are indeed in ascending key order:
`keysAscending` is not vacuously satisfiable. -/
theorem httpsParams_ascending : keysAscending httpsParams :=
  ⟨by decide, by decide, by decide, by decide, trivial⟩

/-- The concrete `cdn.example.com` HTTPS record round-trips through the deployed
reader — a live instance of `svcb_encode_decode` (all its side conditions
discharged), so that theorem is not vacuous. -/
theorem https_real_record_roundtrip :
    typedRData (encodeRData (.svcb 1 httpsTarget httpsParams))
      ⟨{ name := [], rrType := 65, rrClass := 1, ttl := 60,
         rdata := encodeRData (.svcb 1 httpsTarget httpsParams) }, 0⟩
      = some (.svcb 1 httpsTarget httpsParams) := by
  have h := svcb_encode_decode [] [] [] httpsTarget 1 60 1 httpsParams
    (by decide) httpsTarget_ok (by decide) (by decide)
  simpa using h

/-- The concrete HTTPS record decodes to SvcParams that are ascending — a live
instance of `svcparams_sorted`. -/
theorem https_real_record_sorted :
    ∃ ps, typedRData (encodeRData (.svcb 1 httpsTarget httpsParams))
            ⟨{ name := [], rrType := 65, rrClass := 1, ttl := 60,
               rdata := encodeRData (.svcb 1 httpsTarget httpsParams) }, 0⟩
          = some (.svcb 1 httpsTarget ps) ∧ keysAscending ps := by
  have h := svcparams_sorted [] [] [] httpsTarget 1 60 1 httpsParams
    (by decide) httpsTarget_ok (by decide) (by decide) httpsParams_ascending
  simpa using h

/-- HTTPS (type 65) and SVCB (type 64) decode the concrete record identically —
a live instance of `https_record_is_svcb`. -/
theorem https_svcb_same_record :
    typedRData (encodeRData (.svcb 1 httpsTarget httpsParams))
        ⟨{ name := [], rrType := 65, rrClass := 1, ttl := 60,
           rdata := encodeRData (.svcb 1 httpsTarget httpsParams) }, 0⟩
      = typedRData (encodeRData (.svcb 1 httpsTarget httpsParams))
        ⟨{ name := [], rrType := 64, rrClass := 1, ttl := 60,
           rdata := encodeRData (.svcb 1 httpsTarget httpsParams) }, 0⟩ :=
  https_record_is_svcb _ ⟨[], 65, 1, 60, encodeRData (.svcb 1 httpsTarget httpsParams)⟩ 0

end Dns
