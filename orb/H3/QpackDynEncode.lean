/-
H3 QPACK dynamic-table ENCODER-STREAM — the ENCODE side (RFC 9204 §4.1, §4.3, §4.5.1.1).

`H3/Qpack.lean` carries the DEPLOYED encoder-stream PARSER (`decEncInstr`), the
executor (`execInstr` / `execEncoderStream`), the dynamic table (`DynTable.add`,
`keepFit`, the three index resolutions) and the Required-Insert-Count
reconstruction (`reconstructRic`). `QpackDynCorrect.lean` proves the deployed
decode resolves a dynamic-indexed field line to exactly the inserted entry.

This module adds the SEND side an encoder needs and binds it back to those
deployed definitions:

* `encEncInstr` — the encoder-stream instruction ENCODER (the dual of
  `decEncInstr`): Set-Dynamic-Table-Capacity (§4.3.1), Insert with Name Reference
  (§4.3.2), Insert with Literal Name (§4.3.3), Duplicate (§4.3.4). No Huffman
  coding (H = 0), matching the rest of the package.
* `decEncInstr_encInsertLiteral` / `decEncInstr_encInsertStatic` — the encoder is
  inverse to the deployed parser for the two INSERT instructions, so the DEPLOYED
  `execEncoderStream` accepts exactly the encoder's bytes.
* `encRequiredInsertCount` — the §4.5.1.1 EncodedInsertCount the encoder
  transmits, and the field-section ENCODER `encFieldSectionDynIndexed` for a
  dynamic-indexed field line.

The three headline results:

* `dyn_insert_evict` (RFC 9204 §4.3.3, §3.2.2, §4.5.1) — running the DEPLOYED
  encoder-stream executor on the ENCODED insert-with-literal-name bytes, from a
  table that admits the entry, produces a table within capacity whose surviving
  old entries are a PREFIX of the pre-insert table (eviction is oldest-first);
  `dyn_insert_evict_nameref` is the insert-with-static-name-reference companion.
* `dyn_encode_decode` (RFC 9204 §4.5.1.1, §4.5.2) — a field ENCODED against the
  dynamic table (dynamic-indexed relative index 0 under the encoder's own RIC and
  Base) decodes through the DEPLOYED `decodeFieldSection` to EXACTLY the inserted
  field: name resolves to `n`, value to `v`.
* `required_insert_count_correct` (RFC 9204 §4.5.1.1) — the encoder's
  EncodedInsertCount is the exact inverse of the deployed `reconstructRic` over
  the whole valid window (`0` when there are no dynamic references).

Everything is `List UInt8`. Zero sorries; `#print axioms` is the sacred subset
{propext, Quot.sound, Classical.choice}.
-/
import QpackDynCorrect
import H3.QpackEncode

namespace H3
namespace Qpack

open Arena

/-! ## The encoder-stream instruction ENCODER (RFC 9204 §4.3) -/

/-- Encode one encoder-stream instruction to its wire bytes — the dual of the
deployed `decEncInstr`.

* §4.3.1 Set Dynamic Table Capacity: `001 cap(5+)` — pattern `1` over a 5-bit
  prefix.
* §4.3.2 Insert with Name Reference: `1 T idx(6+)` then the value as a raw
  (H = 0) 7-bit-length string — pattern `3` (`T = 1`, static) or `2` (`T = 0`,
  dynamic) over a 6-bit prefix.
* §4.3.3 Insert with Literal Name: `01 H len(5+) name` then the value string —
  name is a raw (H = 0) 5-bit-length string (pattern `2`), value a raw 7-bit one.
* §4.3.4 Duplicate: `000 idx(5+)` — pattern `0` over a 5-bit prefix. -/
def encEncInstr : EncInstr → Bytes
  | .setCapacity cap =>
      encPrefixInt 5 1 cap
  | .insertNameRef isStatic idx value =>
      encPrefixInt 6 (if isStatic then 3 else 2) idx ++ encStr 7 0 value
  | .insertLiteral name value =>
      encStr 5 2 name ++ encStr 7 0 value
  | .duplicate idx =>
      encPrefixInt 5 0 idx

/-! ## Insert-with-literal-name is inverse to the deployed parser (§4.3.3) -/

/-- **`decEncInstr_encInsertLiteral`.** The deployed parser decodes the encoder's
Insert-with-Literal-Name bytes (name and value both within the varint window)
back to exactly that instruction, consuming exactly the encoded bytes and leaving
`tail`. -/
theorem decEncInstr_encInsertLiteral (hd : HuffmanDecoder) (name value tail : Bytes)
    (hn : name.length < 2 ^ 49) (hv : value.length < 2 ^ 49) :
    decEncInstr hd (encEncInstr (.insertLiteral name value) ++ tail)
      = .ok (.insertLiteral name value,
             (encEncInstr (.insertLiteral name value)).length) := by
  obtain ⟨bn, rn, hnenc, hndec⟩ :=
    decStr_encStr hd 5 2 name (encStr 7 0 value ++ tail)
      (by omega) (by omega) (by decide) (by decide) hn
  obtain ⟨bv, rv, hvenc, hvdec⟩ :=
    decStr_encStr hd 7 0 value tail (by omega) (by omega) (by decide) (by decide) hv
  -- rewrite the whole input as `bn :: …`
  have hline : encEncInstr (.insertLiteral name value) ++ tail
      = bn :: (rn ++ (name ++ (bv :: (rv ++ (value ++ tail))))) := by
    show (encStr 5 2 name ++ encStr 7 0 value) ++ tail = _
    unfold encStr
    rw [hnenc, hvenc]
    simp [List.append_assoc]
  rw [hline]
  -- byte class of `bn`: `2·2^5 + r` with `r < 2^5`, so `0x40 ≤ bn < 0x80`.
  have hbn : bn.toNat = 64 + name.length % 32 ∨ bn.toNat = 64 + 31 := by
    unfold encPrefixInt at hnenc
    by_cases hs : name.length < 2 ^ 5 - 1
    · rw [if_pos hs] at hnenc
      injection hnenc with hb _
      left; subst hb
      show (2 * 2 ^ 5 + name.length) % 256 = 64 + name.length % 32
      have : name.length % 32 = name.length := by omega
      omega
    · rw [if_neg hs] at hnenc
      injection hnenc with hb _
      right; subst hb
      show (2 * 2 ^ 5 + (2 ^ 5 - 1)) % 256 = 64 + 31; rfl
  have hbnlt : ¬ 0x80 ≤ bn.toNat := by rcases hbn with h | h <;> omega
  have hbnge : 0x40 ≤ bn.toNat := by rcases hbn with h | h <;> omega
  -- alignment lemmas
  have hnalign : rn ++ (name ++ (encStr 7 0 value ++ tail))
      = rn ++ (name ++ (bv :: (rv ++ (value ++ tail)))) := by
    unfold encStr; rw [hvenc]; simp [List.append_assoc]
  have hvtail : (rn ++ (name ++ (encStr 7 0 value ++ tail))).drop (rn.length + name.length)
      = encStr 7 0 value ++ tail := by
    rw [show rn ++ (name ++ (encStr 7 0 value ++ tail))
          = (rn ++ name) ++ (encStr 7 0 value ++ tail) by simp [List.append_assoc],
        show rn.length + name.length = (rn ++ name).length by simp]
    exact List.drop_left
  have hvcons : encStr 7 0 value ++ tail = bv :: (rv ++ (value ++ tail)) := by
    unfold encStr; rw [hvenc]; simp [List.append_assoc]
  unfold decEncInstr
  dsimp only
  rw [if_neg hbnlt, if_pos hbnge]
  rw [← hnalign, hndec]
  dsimp only
  rw [hvtail, hvcons]
  dsimp only
  rw [hvdec]
  dsimp only
  have hll : (encEncInstr (.insertLiteral name value)).length
      = 1 + (rn.length + name.length) + 1 + (rv.length + value.length) := by
    show (encStr 5 2 name ++ encStr 7 0 value).length = _
    unfold encStr
    rw [hnenc, hvenc]
    simp only [List.length_append, List.length_cons]
    omega
  rw [hll]

/-! ## Insert-with-static-name-reference is inverse to the deployed parser (§4.3.2) -/

/-- **`decEncInstr_encInsertStatic`.** The deployed parser decodes the encoder's
Insert-with-Name-Reference bytes for a STATIC name index (`T = 1`) back to
exactly that instruction, consuming exactly the encoded bytes. -/
theorem decEncInstr_encInsertStatic (hd : HuffmanDecoder) (idx : Nat)
    (value tail : Bytes) (hidx : idx < 2 ^ 49) (hv : value.length < 2 ^ 49) :
    decEncInstr hd (encEncInstr (.insertNameRef true idx value) ++ tail)
      = .ok (.insertNameRef true idx value,
             (encEncInstr (.insertNameRef true idx value)).length) := by
  obtain ⟨bn, rn, hnenc, hndec⟩ :=
    decPrefixInt_encPrefixInt 6 3 idx (encStr 7 0 value ++ tail)
      (by omega) (by omega) (by decide) hidx
  obtain ⟨bv, rv, hvenc, hvdec⟩ :=
    decStr_encStr hd 7 0 value tail (by omega) (by omega) (by decide) (by decide) hv
  have hline : encEncInstr (.insertNameRef true idx value) ++ tail
      = bn :: (rn ++ (bv :: (rv ++ (value ++ tail)))) := by
    show (encPrefixInt 6 3 idx ++ encStr 7 0 value) ++ tail = _
    rw [hnenc]
    unfold encStr; rw [hvenc]
    simp [List.append_assoc]
  rw [hline]
  -- byte class of `bn`: `3·2^6 + r` with `r < 2^6`, so `0xC0 ≤ bn < 0x100`; hence
  -- `0x80 ≤ bn` and `0x40 ≤ bn % 0x80` (the static-name flag T = 1).
  have hbn : bn.toNat = 192 + idx % 64 ∨ bn.toNat = 192 + 63 := by
    unfold encPrefixInt at hnenc
    by_cases hs : idx < 2 ^ 6 - 1
    · rw [if_pos hs] at hnenc
      injection hnenc with hb _
      left; subst hb
      show (3 * 2 ^ 6 + idx) % 256 = 192 + idx % 64
      have : idx % 64 = idx := by omega
      omega
    · rw [if_neg hs] at hnenc
      injection hnenc with hb _
      right; subst hb
      show (3 * 2 ^ 6 + (2 ^ 6 - 1)) % 256 = 192 + 63; rfl
  have hb80 : 0x80 ≤ bn.toNat := by rcases hbn with h | h <;> omega
  have hbT : 0x40 ≤ bn.toNat % 0x80 := by rcases hbn with h | h <;> omega
  -- the value string, aligned
  have hvalign : rn ++ (encStr 7 0 value ++ tail)
      = rn ++ (bv :: (rv ++ (value ++ tail))) := by
    unfold encStr; rw [hvenc]; simp [List.append_assoc]
  have hvtail : (rn ++ (encStr 7 0 value ++ tail)).drop rn.length
      = encStr 7 0 value ++ tail := List.drop_left
  have hvcons : encStr 7 0 value ++ tail = bv :: (rv ++ (value ++ tail)) := by
    unfold encStr; rw [hvenc]; simp [List.append_assoc]
  have hflag : decide (64 ≤ bn.toNat % 128) = true := decide_eq_true hbT
  unfold decEncInstr
  dsimp only
  rw [if_pos hb80, ← hvalign, hndec]
  dsimp only
  rw [hvtail, hvcons]
  dsimp only
  rw [hvdec]
  dsimp only
  rw [hflag]
  have hll : (encEncInstr (.insertNameRef true idx value)).length
      = 1 + rn.length + 1 + (rv.length + value.length) := by
    show (encPrefixInt 6 3 idx ++ encStr 7 0 value).length = _
    rw [hnenc]; unfold encStr; rw [hvenc]
    simp only [List.length_append, List.length_cons]
    omega
  rw [hll]

/-! ## The DEPLOYED executor accepts exactly the encoder's insert bytes -/

/-- Running the DEPLOYED whole-stream executor on the encoder's
Insert-with-Literal-Name bytes is exactly `execInstr` on that instruction. -/
theorem execEncoderStream_encInsertLiteral (hd : HuffmanDecoder) (t : DynTable)
    (name value : Bytes) (hn : name.length < 2 ^ 49) (hv : value.length < 2 ^ 49) :
    execEncoderStream hd t (encEncInstr (.insertLiteral name value))
      = execInstr t (.insertLiteral name value) := by
  -- expose the head so the well-founded `execEncoderStream` step reduces.
  obtain ⟨bn, rn, hnenc, -⟩ :=
    decStr_encStr hd 5 2 name (encStr 7 0 value)
      (by omega) (by omega) (by decide) (by decide) hn
  have hE : encEncInstr (.insertLiteral name value)
      = bn :: (rn ++ name ++ encStr 7 0 value) := by
    show encStr 5 2 name ++ encStr 7 0 value = _
    unfold encStr; rw [hnenc]; simp [List.append_assoc]
  have hround : decEncInstr hd (encEncInstr (.insertLiteral name value))
      = .ok (.insertLiteral name value, (encEncInstr (.insertLiteral name value)).length) := by
    have := decEncInstr_encInsertLiteral hd name value [] hn hv
    rwa [List.append_nil] at this
  rw [hE, execEncoderStream, ← hE, hround]
  dsimp only
  cases hexec : execInstr t (.insertLiteral name value) with
  | error e => rfl
  | ok t' => simp only [List.drop_length, execEncoderStream]

/-- Running the DEPLOYED whole-stream executor on the encoder's
Insert-with-Name-Reference (static) bytes is exactly `execInstr` on that
instruction. -/
theorem execEncoderStream_encInsertStatic (hd : HuffmanDecoder) (t : DynTable)
    (idx : Nat) (value : Bytes) (hidx : idx < 2 ^ 49) (hv : value.length < 2 ^ 49) :
    execEncoderStream hd t (encEncInstr (.insertNameRef true idx value))
      = execInstr t (.insertNameRef true idx value) := by
  obtain ⟨bn, rn, hnenc, -⟩ :=
    decPrefixInt_encPrefixInt 6 3 idx (encStr 7 0 value)
      (by omega) (by omega) (by decide) hidx
  have hE : encEncInstr (.insertNameRef true idx value)
      = bn :: (rn ++ encStr 7 0 value) := by
    show encPrefixInt 6 3 idx ++ encStr 7 0 value = _
    rw [hnenc]; simp [List.append_assoc]
  have hround : decEncInstr hd (encEncInstr (.insertNameRef true idx value))
      = .ok (.insertNameRef true idx value,
             (encEncInstr (.insertNameRef true idx value)).length) := by
    have := decEncInstr_encInsertStatic hd idx value [] hidx hv
    rwa [List.append_nil] at this
  rw [hE, execEncoderStream, ← hE, hround]
  dsimp only
  cases hexec : execInstr t (.insertNameRef true idx value) with
  | error e => rfl
  | ok t' => simp only [List.drop_length, execEncoderStream]

/-! ## Headline theorem 1 — encoder-stream insert + eviction stays within capacity -/

/-- **`dyn_insert_evict` (RFC 9204 §4.3.3, §3.2.2, §4.5.1).** Feed the DEPLOYED
encoder-stream executor the ENCODED Insert-with-Literal-Name bytes for
`(name, value)`, from a table whose current capacity admits the entry. The
executor ACCEPTS; the resulting table

* is exactly the deployed insert `t.add name value`,
* stays WITHIN CAPACITY (`Fits`: `tableSize ≤ maxSize`), and
* evicts strictly from the OLD end — the surviving old entries (`entries.tail`)
  are a PREFIX of the pre-insert table.

A `keepFit` that dropped a NEWEST entry, or an insert that overflowed the
capacity, would break the prefix / `Fits` clauses; the entry is real
(`name`/`value` arbitrary within the varint window). -/
theorem dyn_insert_evict (hd : HuffmanDecoder) (t : DynTable) (name value : Bytes)
    (hfit : entrySize (name, value) ≤ t.maxSize)
    (hn : name.length < 2 ^ 49) (hv : value.length < 2 ^ 49) :
    ∃ t', execEncoderStream hd t (encEncInstr (.insertLiteral name value)) = .ok t'
        ∧ t' = t.add name value
        ∧ t'.Fits
        ∧ (∃ suf, t'.entries.tail ++ suf = t.entries) := by
  have hexec : execInstr t (.insertLiteral name value) = .ok (t.add name value) := by
    show (if entrySize (name, value) ≤ t.maxSize then Except.ok (t.add name value)
          else Except.error Err.encoderStream) = _
    rw [if_pos hfit]
  refine ⟨t.add name value, ?_, rfl, add_fits t name value, ?_⟩
  · rw [execEncoderStream_encInsertLiteral hd t name value hn hv, hexec]
  · -- eviction oldest-first: entries.tail = keepFit t.entries _, a prefix of t.entries
    have htail : (t.add name value).entries.tail
        = keepFit t.entries (t.maxSize - entrySize (name, value)) := by
      rw [add_entries_fit t name value hfit]; rfl
    rw [htail]
    exact keepFit_prefix t.entries (t.maxSize - entrySize (name, value))

/-- **`dyn_insert_evict_nameref` (RFC 9204 §4.3.2, §3.2.2).** The static
Insert-with-Name-Reference companion: from the encoder's bytes, the DEPLOYED
executor inserts the static entry's name with the given value and stays within
capacity. -/
theorem dyn_insert_evict_nameref (hd : HuffmanDecoder) (t : DynTable) (idx : Nat)
    (sname svalue : String) (value : Bytes)
    (hentry : staticEntry idx = some (sname, svalue))
    (hfit : entrySize (strBytes sname, value) ≤ t.maxSize)
    (hidx : idx < 2 ^ 49) (hv : value.length < 2 ^ 49) :
    ∃ t', execEncoderStream hd t (encEncInstr (.insertNameRef true idx value)) = .ok t'
        ∧ t' = t.add (strBytes sname) value
        ∧ t'.Fits
        ∧ (∃ suf, t'.entries.tail ++ suf = t.entries) := by
  have hexec : execInstr t (.insertNameRef true idx value)
      = .ok (t.add (strBytes sname) value) :=
    execInstr_insertStatic_correct t idx sname svalue value hentry hfit
  refine ⟨t.add (strBytes sname) value, ?_, rfl, add_fits t _ _, ?_⟩
  · rw [execEncoderStream_encInsertStatic hd t idx value hidx hv, hexec]
  · have htail : (t.add (strBytes sname) value).entries.tail
        = keepFit t.entries (t.maxSize - entrySize (strBytes sname, value)) := by
      rw [add_entries_fit t (strBytes sname) value hfit]; rfl
    rw [htail]
    exact keepFit_prefix t.entries (t.maxSize - entrySize (strBytes sname, value))

/-! ## Headline theorem 3 — the EncodedInsertCount is inverse to the reconstruction -/

/-- **The §4.5.1.1 EncodedInsertCount the encoder transmits.** For no dynamic
references (`reqIC = 0`) it is `0`; otherwise `ReqInsertCount mod (2·MaxEntries)
+ 1`, where `MaxEntries = MaxTableCapacity / 32`. -/
def encRequiredInsertCount (maxEntries reqIC : Nat) : Nat :=
  if reqIC = 0 then 0 else reqIC % (2 * maxEntries) + 1

/-- **`required_insert_count_correct` (RFC 9204 §4.5.1.1).** The deployed
`reconstructRic` is the exact inverse of the encoder's `encRequiredInsertCount`
for every Required Insert Count in the valid window
`reqIC ≤ totalInserts + MaxEntries < reqIC + 2·MaxEntries` (the `reqIC = 0`
no-references case included). -/
theorem required_insert_count_correct (me ti reqIC : Nat) (hme : 0 < me)
    (hle : reqIC ≤ ti + me) (hwin : ti + me < reqIC + 2 * me) :
    reconstructRic me ti (encRequiredInsertCount me reqIC) = .ok reqIC := by
  unfold encRequiredInsertCount
  by_cases h0 : reqIC = 0
  · subst h0; simp
  · rw [if_neg h0]
    exact reconstructRic_correct me ti reqIC hme (Nat.pos_of_ne_zero h0) hle hwin

/-- A mutant EncodedInsertCount that is off by the wrap period reconstructs to a
DIFFERENT Required Insert Count — the encoder's value is load-bearing, not
vacuous. (Concrete: `MaxEntries = 4`, no prior inserts, `reqIC = 1`: the correct
`encRIC = 2` reconstructs to `1`, but `encRIC = 3` reconstructs to `2`.) -/
theorem required_insert_count_mutant :
    reconstructRic 4 0 (encRequiredInsertCount 4 1) = .ok 1 ∧
      reconstructRic 4 0 (encRequiredInsertCount 4 1 + 1) = .ok 2 := by
  constructor
  · rfl
  · rfl

/-! ## Headline theorem 2 — a field encoded against the table decodes to that field -/

/-- Encode a dynamic-indexed field line for RELATIVE index `relIdx`
(RFC 9204 §4.5.2, `1 T=0 idx(6+)`): pattern `2` over a 6-bit prefix. -/
def encIndexedDynLine (relIdx : Nat) : Bytes := encPrefixInt 6 2 relIdx

/-- Encode a whole field section that references the dynamic table with a single
dynamic-indexed field line: the §4.5.1 section prefix (EncodedInsertCount on an
8-bit prefix, Delta Base on a 7-bit prefix with sign clear) followed by the
indexed dynamic line. -/
def encFieldSectionDynIndexed (encRic deltaBase relIdx : Nat) : Bytes :=
  encPrefixInt 8 0 encRic ++ encPrefixInt 7 0 deltaBase ++ encIndexedDynLine relIdx

/-- **`dyn_encode_decode` (RFC 9204 §4.5.1.1, §4.5.2).** Insert `(n, v)` into a
fresh dynamic table (`insertCount = 0`) whose capacity admits it and whose
advertised bound is at least one entry (`32 ≤ maxCapacity`). ENCODE a field
section that references that entry by dynamic relative index 0 — under the
encoder's own EncodedInsertCount (`encRequiredInsertCount MaxEntries 1`) and a
zero Delta Base. The DEPLOYED `decodeFieldSection`, given the table after the
insert, ACCEPTS the encoder's bytes, yields exactly one regular field `⟨ne, ve⟩`
and no pseudo-headers, and the decoded field RESOLVES to EXACTLY the inserted
entry: `ne → n`, `ve → v`.

A resolver returning nothing fails acceptance; a resolution to a different entry
fails the byte-equality; the encoder value is load-bearing (see
`deployed_rejects_dynamic_indexed`, which refutes the same shape against the
empty table). Holds for every Huffman-decoder behavior (H = 0 throughout). -/
theorem dyn_encode_decode (hd : HuffmanDecoder) (t : DynTable) (n v : Bytes)
    (hic0 : t.insertCount = 0) (hs : entrySize (n, v) ≤ t.maxSize)
    (hcap : 32 ≤ t.maxCapacity) (hcl : classifyName n = none)
    (hroom : n.length + v.length < sidecarBaseNat) :
    ∃ (r : Decoded) (ne ve : Entry),
      decodeFieldSection hd emptyStore
          (encFieldSectionDynIndexed (encRequiredInsertCount (t.maxCapacity / 32) 1) 0 0)
          (t.add n v) = .ok r ∧
      r.fields = [⟨ne, ve⟩] ∧ r.pseudo = {} ∧
      r.store.resolve ne = some n.toArray ∧
      r.store.resolve ve = some v.toArray := by
  -- MaxEntries ≥ 1, so the encoder's RIC for one insert is `1 % (2·me) + 1 = 2`.
  have hme : 1 ≤ t.maxCapacity / 32 :=
    (Nat.le_div_iff_mul_le (by omega : 0 < 32)).mpr (by omega)
  have hric : encRequiredInsertCount (t.maxCapacity / 32) 1 = 2 := by
    unfold encRequiredInsertCount
    rw [if_neg (by decide)]
    have : (1 : Nat) % (2 * (t.maxCapacity / 32)) = 1 := Nat.mod_eq_of_lt (by omega)
    rw [this]
  -- the encoded section is exactly the deployed wire vector `02 00 80`.
  have hbytes : encFieldSectionDynIndexed
      (encRequiredInsertCount (t.maxCapacity / 32) 1) 0 0 = [0x02, 0x00, 0x80] := by
    rw [hric]; decide
  rw [hbytes]
  exact deployed_decodes_dynamic_indexed hd t n v hic0 hs hcap hcl hroom

/-! ## Executable wire vectors, checker-verified -/

/-- A Huffman decoder that rejects everything — never consulted (H = 0). -/
private def rejectAllHuffmanE : HuffmanDecoder := ⟨fun _ => none⟩

-- The encoder-stream instruction encodings (RFC 9204 §4.3 first bytes).
#guard encEncInstr (.setCapacity 100) = encPrefixInt 5 1 100
#guard encEncInstr (.duplicate 3) = [0x03]
-- Insert with static name reference 0, empty value: `0xc0 0x00`.
#guard encEncInstr (.insertNameRef true 0 []) = [0xc0, 0x00]
-- Insert with literal name "" and empty value: `0x40 0x00`.
#guard encEncInstr (.insertLiteral [] []) = [0x40, 0x00]

-- The field-section encoder produces the deployed dynamic-indexed vector.
#guard encFieldSectionDynIndexed 2 0 0 = [0x02, 0x00, 0x80]

-- The EncodedInsertCount round trips through the deployed reconstruction.
private def vecRicRoundTrip : Bool :=
  (match reconstructRic 4 0 (encRequiredInsertCount 4 1) with
   | .ok 1 => true | _ => false)
    && (encRequiredInsertCount 4 0 == 0)
    && (match reconstructRic 4 0 (encRequiredInsertCount 4 0) with
        | .ok 0 => true | _ => false)
#guard vecRicRoundTrip

-- The DEPLOYED executor accepts the encoder's Insert-with-Literal-Name bytes and
-- lands the entry in the table (advertised capacity 4096, current 200).
private def vecInsertLiteral : Bool :=
  match execEncoderStream rejectAllHuffmanE
      ((DynTable.advertised 4096).setCapacity 200)
      (encEncInstr (.insertLiteral (strBytes "custom-key") (strBytes "custom-value"))) with
  | .ok t =>
    t.insertCount == 1 && t.entries.length == 1
      && (t.byAbs 0 == some (strBytes "custom-key", strBytes "custom-value"))
      && decide (tableSize t.entries ≤ t.maxSize)
  | .error _ => false
#guard vecInsertLiteral

/-! ## Axiom audit -/

#print axioms dyn_insert_evict
#print axioms dyn_insert_evict_nameref
#print axioms dyn_encode_decode
#print axioms required_insert_count_correct
#print axioms decEncInstr_encInsertLiteral
#print axioms decEncInstr_encInsertStatic
#print axioms execEncoderStream_encInsertLiteral
#print axioms execEncoderStream_encInsertStatic
#print axioms required_insert_count_mutant

end Qpack
end H3
