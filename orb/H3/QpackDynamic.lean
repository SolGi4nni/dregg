/-
H3 QPACK dynamic table — the LEDGER h3.qpackdyn lane (RFC 9204 §2.1.2, §3.2, §4.5).

This is a breadth leaf library: it proves the three RFC-conformant properties of
the QPACK dynamic table that a decoder must uphold, over the DEPLOYED definitions
of `H3/Qpack.lean` (`DynTable`, `DynTable.add`, `keepFit`, the index resolutions,
and the deployed `decodeFieldSection`). No new executable — the theorems bind
directly to the code the deployed QUIC/H3 lane runs.

Three headline theorems (each with real, non-vacuous hypotheses):

* `qpack_dynamic_insert` (§3.2.2, §3.2.4) — inserting a fitting entry makes it the
  NEWEST entry, advances the insert count, keeps the table within its maximum, and
  when the new entry cannot coexist with everything already stored, eviction removes
  STRICTLY the OLDEST entries (the survivors are a proper prefix, strictly fewer).

* `qpack_dynamic_ref` (§3.2.5 / §4.5.2) — a field line that REFERENCES a dynamic
  entry decodes to EXACTLY that entry. Run the deployed `decodeFieldSection` on the
  wire bytes `02 00 80` (Required Insert Count 1 → Base 1, then an indexed dynamic
  field line at relative index 0) against the table AFTER inserting `(n, v)`: the
  decode accepts and the emitted field resolves byte-for-byte to `(n, v)`.

* `qpack_blocked_stream` (§2.1.2) — a reference to a not-yet-received insert BLOCKS:
  the IDENTICAL wire `02 00 80` decoded against the table BEFORE the insert is
  applied (`insertCount = 0`, so the reconstructed Required Insert Count 1 exceeds
  the inserts received) is rejected with `Err.dynamicUnsupported` — no decode of an
  unavailable entry. `qpack_blocked_then_acked` pairs the two: the same bytes block
  before the insert and decode to the entry after it.

The `HuffmanDecoder` is the abstract oracle (RFC 7541 Appendix B code the client
emits); every theorem here holds uniformly over every decoder behavior — none of
these vectors sets the Huffman bit, so the oracle is never consulted, and no crypto
is invoked. Zero sorries; `#print axioms` is the sacred subset
{propext, Quot.sound, Classical.choice}.
-/
import QpackSound

namespace H3
namespace Qpack
namespace Dynamic

open Arena

/-! ## Projection lemmas for the fitting insert (local, over ground-truth `add`) -/

private theorem add_ent (t : DynTable) (n v : Bytes) (hs : entrySize (n, v) ≤ t.maxSize) :
    (t.add n v).entries = (n, v) :: keepFit t.entries (t.maxSize - entrySize (n, v)) := by
  unfold DynTable.add; rw [if_pos hs]

private theorem add_ic (t : DynTable) (n v : Bytes) (hs : entrySize (n, v) ≤ t.maxSize) :
    (t.add n v).insertCount = t.insertCount + 1 := by
  unfold DynTable.add; rw [if_pos hs]

/-! ## Headline 1 — insert adds the newest entry and evicts strictly the oldest -/

/-- **`qpack_dynamic_insert` (RFC 9204 §3.2.2, §3.2.4).** Inserting a fitting
`(n, v)` (`entrySize (n, v) ≤ maxSize`) makes it the NEWEST entry (list head),
advances the insert count by one, and keeps the table within its maximum size.
When the new entry additionally cannot coexist with everything already stored
(`maxSize < entrySize (n, v) + tableSize entries`), the insert evicts STRICTLY the
OLDEST entries: the survivors are a proper PREFIX of the pre-insert table (strictly
fewer). The `hs` hypothesis is load-bearing — an oversize insert stores nothing
(`add` returns the empty table), so `head?` would be `none`. -/
theorem qpack_dynamic_insert (t : DynTable) (n v : Bytes)
    (hs : entrySize (n, v) ≤ t.maxSize) :
    (t.add n v).entries.head? = some (n, v)
    ∧ (t.add n v).insertCount = t.insertCount + 1
    ∧ tableSize (t.add n v).entries ≤ t.maxSize
    ∧ (t.maxSize < entrySize (n, v) + tableSize t.entries →
        (t.add n v).entries.tail <+: t.entries ∧
        (t.add n v).entries.tail.length < t.entries.length) := by
  have hent := add_ent t n v hs
  have htail : (t.add n v).entries.tail
      = keepFit t.entries (t.maxSize - entrySize (n, v)) := by rw [hent]; rfl
  refine ⟨by rw [hent]; rfl, add_ic t n v hs, ?_, ?_⟩
  · rw [hent, tableSize_cons]
    have := keepFit_size t.entries (t.maxSize - entrySize (n, v))
    omega
  · intro hfull
    obtain ⟨suf, hsuf⟩ := keepFit_prefix t.entries (t.maxSize - entrySize (n, v))
    have hks := keepFit_size t.entries (t.maxSize - entrySize (n, v))
    have hsuf_ne : suf ≠ [] := by
      intro hnil; rw [hnil, List.append_nil] at hsuf; rw [hsuf] at hks; omega
    have hlen : (keepFit t.entries (t.maxSize - entrySize (n, v))).length
        < t.entries.length := by
      have := congrArg List.length hsuf
      rw [List.length_append] at this
      have hpos : 0 < suf.length := List.length_pos_iff.mpr hsuf_ne
      omega
    exact ⟨by rw [htail]; exact ⟨suf, hsuf⟩, by rw [htail]; exact hlen⟩

/-! ## Reduction lemmas for the concrete dynamic-indexed wire vector -/

/-- The 8-bit prefix integer `0x02` (value `2 < 255`) decodes to `2`, no
continuation — the encoded Required Insert Count of the `02 00 80` vector. -/
private theorem decPrefixInt8_two (rest : Bytes) :
    decPrefixInt 8 0x02 rest = some (2, 0) := by
  unfold decPrefixInt; rfl

/-- The 6-bit prefix in `0x80` (`1 0 000000`) decodes to `0` — relative index 0 of
the indexed dynamic field line. -/
private theorem decPrefixInt6_dyn0 : decPrefixInt 6 (0x80 : UInt8) [] = some (0, 0) := by
  decide

/-- §4.5.1.1 reconstruction against the table AFTER one insert (insert total 1):
encoded Required Insert Count 2 reconstructs Required Insert Count 1 — the general
inverse `reconstructRic_correct` at `ric = 1`, `totalInserts = 1`. -/
private theorem recRic_two (mx : Nat) (h : 32 ≤ mx) :
    reconstructRic (mx / 32) 1 2 = .ok 1 := by
  have hme : 0 < mx / 32 :=
    (Nat.le_div_iff_mul_le (by omega : 0 < 32)).mpr (by omega)
  have h2 : (1 : Nat) % (2 * (mx / 32)) = 1 := Nat.mod_eq_of_lt (by omega)
  have hcor := reconstructRic_correct (mx / 32) 1 1 hme (by omega) (by omega) (by omega)
  rwa [h2] at hcor

/-- §4.5.1.1 reconstruction against the table BEFORE the insert (insert total 0):
the SAME encoded Required Insert Count 2 reconstructs Required Insert Count 1, which
now exceeds the insert total — the blocked-stream condition. -/
private theorem recRic_blocked (mx : Nat) (h : 32 ≤ mx) :
    reconstructRic (mx / 32) 0 2 = .ok 1 := by
  have hme : 0 < mx / 32 :=
    (Nat.le_div_iff_mul_le (by omega : 0 < 32)).mpr (by omega)
  have h2 : (1 : Nat) % (2 * (mx / 32)) = 1 := Nat.mod_eq_of_lt (by omega)
  have hcor := reconstructRic_correct (mx / 32) 0 1 hme (by omega) (by omega) (by omega)
  rwa [h2] at hcor

/-- The just-inserted entry is named by RELATIVE index 0 against Base 1, resolving
to EXACTLY `(n, v)` (§3.2.5). -/
private theorem add_rel0 (t : DynTable) (n v : Bytes) (hic0 : t.insertCount = 0)
    (hs : entrySize (n, v) ≤ t.maxSize) :
    (t.add n v).byRelative 1 0 = some (n, v) := by
  unfold DynTable.byRelative DynTable.byAbs
  rw [add_ic t n v hs, hic0, if_pos (by omega : (0 : Nat) < 1),
    if_pos (by omega : (1 - 1 - 0 : Nat) < 0 + 1), add_ent t n v hs]
  have hidx : (0 + 1 - 1 - (1 - 1 - 0) : Nat) = 0 := by omega
  rw [hidx]; simp

/-- One field line that yields a regular field and then exhausts the input runs the
loop to that single field (the single-line reduction of `decodeLines`). -/
private theorem decodeLines_single (hd : HuffmanDecoder) (st st' : Store)
    (b : UInt8) (rest : Bytes) (fl : FieldLine) (nn : Nat)
    (dyn : DynTable) (base : Nat)
    (hone : decodeOneLine hd st (b :: rest) dyn base = .ok (st', .field fl, nn))
    (hdrop : (b :: rest).drop nn = []) :
    decodeLines hd st (b :: rest) {} [] dyn base = .ok (st', {}, [fl]) := by
  rw [decodeLines]
  split
  · rename_i e heq; rw [hone] at heq; exact absurd heq (by simp)
  · rename_i st'' out n' heq
    rw [hone] at heq
    simp only [Except.ok.injEq, Prod.mk.injEq] at heq
    obtain ⟨hsx, hout, hn⟩ := heq
    subst hsx; subst hout; subst hn
    simp only [hdrop]
    rw [decodeLines]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]

/-! ## Headline 2 — the DEPLOYED decode resolves a dynamic reference to its entry -/

/-- **`qpack_dynamic_ref` (RFC 9204 §4.5.2, indexed dynamic `T = 0`).** Insert
`(n, v)` into a fresh dynamic table (`insertCount = 0`) whose maximum accommodates
it, then run the DEPLOYED `decodeFieldSection` on the wire bytes `02 00 80` — a
section prefix (encoded Required Insert Count 1 → Base 1) followed by an indexed
dynamic field line at relative index 0. The decode ACCEPTS, yields exactly one
regular field `⟨ne, ve⟩`, and the decoded field RESOLVES to EXACTLY the inserted
entry: `ne → n`, `ve → v`, byte for byte. Holds for every Huffman-decoder behavior
(the Huffman bit is never set). A resolver that returned no entry would fail the
acceptance; a resolution to a different entry would fail the byte-equality. -/
theorem qpack_dynamic_ref (hd : HuffmanDecoder) (t : DynTable)
    (n v : Bytes) (hic0 : t.insertCount = 0)
    (hs : entrySize (n, v) ≤ t.maxSize) (hcap : 32 ≤ t.maxCapacity)
    (hcl : classifyName n = none)
    (hroom : n.length + v.length < sidecarBaseNat) :
    ∃ (r : Decoded) (ne ve : Entry),
      decodeFieldSection hd emptyStore [0x02, 0x00, 0x80] (t.add n v) = .ok r ∧
      r.fields = [⟨ne, ve⟩] ∧
      r.store.resolve ne = some n.toArray ∧
      r.store.resolve ve = some v.toArray := by
  have hrel := add_rel0 t n v hic0 hs
  have hroom' : emptyStore.sidecar.size + n.length + v.length < sidecarBaseNat := by
    show 0 + n.length + v.length < sidecarBaseNat; omega
  obtain ⟨st', ne, ve, hem, hrn, hrv⟩ := emitField_field_ok emptyStore n v hcl hroom'
  have hb80 : ((0x80 : Nat) ≤ (0x80 : UInt8).toNat) = True := eq_true (by decide)
  have hb40 : ((0x40 : Nat) ≤ (0x80 : UInt8).toNat % 0x80) = False := eq_false (by decide)
  have hone : decodeOneLine hd emptyStore [0x80] (t.add n v) 1
      = .ok (st', .field ⟨ne, ve⟩, 1) := by
    unfold decodeOneLine
    simp only [hb80, hb40, reduceIte, decPrefixInt6_dyn0, hrel, hem, Nat.add_zero]
  have hdrop : ([0x80] : Bytes).drop 1 = [] := rfl
  have hlines := decodeLines_single hd emptyStore st' 0x80 [] ⟨ne, ve⟩ 1
    (t.add n v) 1 hone hdrop
  refine ⟨⟨st', {}, [⟨ne, ve⟩]⟩, ne, ve, ?_, rfl, hrn, hrv⟩
  have hric : reconstructRic (t.maxCapacity / 32) 1 2 = .ok 1 := recRic_two t.maxCapacity hcap
  have hic1 : (t.add n v).insertCount = 1 := by rw [add_ic t n v hs, hic0]
  unfold decodeFieldSection
  simp only [decPrefixInt8_two, List.drop_zero, decPrefixInt7_zero,
    add_maxCapacity, hic1, hric, reconstructBase_zeroByte, Nat.add_zero,
    Nat.lt_irrefl, reduceIte, hlines]

/-! ## Headline 3 — a reference to a not-yet-received insert BLOCKS (§2.1.2) -/

/-- **`qpack_blocked_stream` (RFC 9204 §2.1.2).** The SAME wire bytes `02 00 80`
whose Required Insert Count reconstructs to 1, decoded against a table that has
received NO inserts yet (`insertCount = 0`), is rejected with
`Err.dynamicUnsupported`: the Required Insert Count exceeds the inserts the decoder
has received, so the reference names an entry it does not yet have — the decode
BLOCKS rather than resolving an unavailable entry. The `insertCount = 0` hypothesis
is load-bearing: after the insert is received (`insertCount = 1`) the identical
bytes DECODE (`qpack_dynamic_ref`). Holds for every store and Huffman decoder. -/
theorem qpack_blocked_stream (hd : HuffmanDecoder) (st : Store) (t : DynTable)
    (hic0 : t.insertCount = 0) (hcap : 32 ≤ t.maxCapacity) :
    decodeFieldSection hd st [0x02, 0x00, 0x80] t = .error .dynamicUnsupported := by
  have hric : reconstructRic (t.maxCapacity / 32) 0 2 = .ok 1 :=
    recRic_blocked t.maxCapacity hcap
  unfold decodeFieldSection
  simp only [decPrefixInt8_two, List.drop_zero, decPrefixInt7_zero, hic0,
    hric, reconstructBase_zeroByte, Nat.add_zero, Nat.zero_lt_one, reduceIte]

/-- **`qpack_blocked_then_acked` (RFC 9204 §2.1.2).** The blocked/unblocked pair on
IDENTICAL wire bytes: `02 00 80` decoded against the table BEFORE the insert is
received BLOCKS with `Err.dynamicUnsupported`; decoded against the table AFTER the
insert `(n, v)` is applied, it DECODES to exactly that entry. This is the
"blocks until acked — no decode of unavailable" story end to end. -/
theorem qpack_blocked_then_acked (hd : HuffmanDecoder) (t : DynTable)
    (n v : Bytes) (hic0 : t.insertCount = 0)
    (hs : entrySize (n, v) ≤ t.maxSize) (hcap : 32 ≤ t.maxCapacity)
    (hcl : classifyName n = none)
    (hroom : n.length + v.length < sidecarBaseNat) :
    decodeFieldSection hd emptyStore [0x02, 0x00, 0x80] t = .error .dynamicUnsupported
    ∧ ∃ (r : Decoded) (ne ve : Entry),
        decodeFieldSection hd emptyStore [0x02, 0x00, 0x80] (t.add n v) = .ok r ∧
        r.fields = [⟨ne, ve⟩] ∧
        r.store.resolve ne = some n.toArray ∧
        r.store.resolve ve = some v.toArray :=
  ⟨qpack_blocked_stream hd emptyStore t hic0 hcap,
   qpack_dynamic_ref hd t n v hic0 hs hcap hcl hroom⟩

/-! ## Non-vacuity witnesses (kernel-reducible `#guard`) -/

-- A 70-octet table. Insert e0 (size 32), then e1 (size 33): 65 ≤ 70, both fit.
-- Inserting e2 (size 33) makes 98 > 70, so the OLDEST, e0, is evicted.
private def w0 : DynTable := ⟨[], 0, 70, 70⟩
private def wTwo : DynTable := (w0.add [] []).add [1] []
private def wThree : DynTable := wTwo.add [2] []

-- The fitting insert fires the eviction branch: two entries remain, not three.
#guard wThree.insertCount == 3
#guard wThree.entries.length == 2
#guard wThree.entries.head? == some ([2], [])          -- newest is the just-inserted entry
#guard decide (tableSize wThree.entries ≤ wThree.maxSize)
#guard wThree.byRelative 3 0 == some ([2], [])         -- relative 0 names the newest
#guard wThree.byAbs 0 == none                          -- evicted oldest no longer resolves

-- An OVERSIZE insert (entry 40 > maxSize 35) stores nothing — the `hs` hypothesis
-- of `qpack_dynamic_insert` is genuinely restrictive, not vacuous.
private def wSmall : DynTable := ⟨[([9], [])], 1, 35, 35⟩
#guard (wSmall.add (List.replicate 9 0) []).entries == ([] : List Pair)

/-! ## Axiom audit (fully-qualified, nested 3-deep) -/

#print axioms H3.Qpack.Dynamic.qpack_dynamic_insert
#print axioms H3.Qpack.Dynamic.qpack_dynamic_ref
#print axioms H3.Qpack.Dynamic.qpack_blocked_stream
#print axioms H3.Qpack.Dynamic.qpack_blocked_then_acked

end Dynamic
end Qpack
end H3
