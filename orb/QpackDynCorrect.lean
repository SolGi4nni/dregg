/-
H3 QPACK dynamic table — the CORRECTNESS theory (RFC 9204 §3.2, §4.5).

`H3/Qpack.lean` now carries the DEPLOYED QPACK dynamic table: a FIFO `DynTable` of
(name, value) pairs with size-bounded oldest-first eviction (`keepFit`, `add`) and
the three index resolutions — ABSOLUTE (§3.2.4), RELATIVE against the section Base
(§3.2.5 / §4.5.2), and POST-BASE (§3.2.6 / §4.5.3). The field-section decoder
`decodeFieldSection` resolves a dynamic-indexed field line against a supplied
`DynTable`; a reference out of range for that table fails with
`Err.dynamicUnsupported`.

This file supplies the CORRECTNESS story over exactly those deployed definitions:

* a declarative insertion specification (`AddSpec`) and the refinement
  `qpack_dyntable_add_refines_spec` that the operational `DynTable.add` satisfies;
* the insert-then-index round trip at each index kind
  (`qpack_dyntable_abs_correct` / `_relative_correct` / `_postbase_correct`): after
  inserting `(n, v)` (fitting the maximum), the just-inserted entry is named by
  absolute index `insertCount`, by relative 0 against the post-insert Base, and by
  post-base 0 against the pre-insert Base, and each reference resolves to EXACTLY
  `(n, v)`;
* the DEPLOYED-DECODE binding `deployed_decodes_dynamic_indexed`: on the wire bytes
  of a dynamic-indexed field line, the real `decodeFieldSection` — given the table
  after inserting `(n, v)` — decodes to a store whose emitted field RESOLVES to
  exactly `(n, v)`. The OLD stub returned `Err.dynamicUnsupported` for these same
  bytes (`deployed_rejects_dynamic_indexed` / `deployed_rejects_postbase` still
  hold against the EMPTY table), so the stub position is refuted at the deployed
  level, and a wrong index resolution refutes the byte-equality;
* `qpack_dyntable_evict_correct`: eviction removes strictly the OLDEST entries and
  restores the size bound.

Zero sorries; `#print axioms` is the sacred subset {propext, Quot.sound,
Classical.choice}.
-/
import QpackSound

namespace H3
namespace Qpack

open Arena

/-! ## `add` — projection lemmas -/

theorem add_entries_fit (t : DynTable) (n v : Bytes)
    (hs : entrySize (n, v) ≤ t.maxSize) :
    (t.add n v).entries = (n, v) :: keepFit t.entries (t.maxSize - entrySize (n, v)) := by
  unfold DynTable.add; rw [if_pos hs]

theorem add_insertCount_fit (t : DynTable) (n v : Bytes)
    (hs : entrySize (n, v) ≤ t.maxSize) :
    (t.add n v).insertCount = t.insertCount + 1 := by
  unfold DynTable.add; rw [if_pos hs]

theorem add_maxSize (t : DynTable) (n v : Bytes) :
    (t.add n v).maxSize = t.maxSize := by
  unfold DynTable.add; split <;> rfl

/-! ## The CORRECTNESS specification (RFC 9204 §3.2.2, §3.2.4) -/

/-- **The RFC-conformant insertion specification.** Given a dynamic table listed
newest-first as `pre` with maximum size `max`, inserting `(n, v)` must produce a
list `post` satisfying, declaratively:

* `newest` (§3.2.4): when the entry fits the maximum, it becomes the newest entry
  — the head of `post`.
* `onlyOldestEvicted` (§4.5.1): when the entry fits, the entries surviving from
  `pre` are a PREFIX of `pre` (the newest ones).
* `withinMax` (§3.2.2): when the entry fits, the resulting table size does not
  exceed the maximum.
* `oversizeEmpties` (§3.2.2): an entry larger than the maximum stores nothing.

This is a specification, not the implementation: it constrains `post` through
`head?`, `IsPrefix`, and a size bound, never mentioning how eviction is computed. -/
structure AddSpec (pre : List Pair) (max : Nat) (n v : Bytes) (post : List Pair) :
    Prop where
  newest : entrySize (n, v) ≤ max → post.head? = some (n, v)
  onlyOldestEvicted : entrySize (n, v) ≤ max → ∃ suf, post.tail ++ suf = pre
  withinMax : entrySize (n, v) ≤ max → tableSize post ≤ max
  oversizeEmpties : max < entrySize (n, v) → post = []

/-- **The refinement theorem.** The operational `DynTable.add` (the deployed
insertion in `H3/Qpack.lean`) satisfies the declarative `AddSpec` on every table
and every entry. -/
theorem qpack_dyntable_add_refines_spec (t : DynTable) (n v : Bytes) :
    AddSpec t.entries t.maxSize n v (t.add n v).entries := by
  by_cases hs : entrySize (n, v) ≤ t.maxSize
  · have hadd := add_entries_fit t n v hs
    refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun hover => ?_⟩
    · rw [hadd]; rfl
    · rw [hadd]; simpa using keepFit_prefix t.entries (t.maxSize - entrySize (n, v))
    · rw [hadd, tableSize_cons]
      have := keepFit_size t.entries (t.maxSize - entrySize (n, v))
      omega
    · omega
  · have hadd : (t.add n v).entries = [] := by
      unfold DynTable.add; rw [if_neg hs]
    refine ⟨fun h => absurd h hs, fun h => absurd h hs, fun h => absurd h hs,
      fun _ => hadd⟩

/-! ## Headline theorem 1 — indexed decode of the just-inserted entry -/

/-- **`qpack_dyntable_abs_correct` (RFC 9204 §3.2.4).** After inserting `(n, v)`
into a dynamic table whose maximum accommodates it, the ABSOLUTE index that names
the just-inserted entry is the pre-insert `insertCount`, and it resolves to
EXACTLY `(n, v)`. -/
theorem qpack_dyntable_abs_correct (t : DynTable) (n v : Bytes)
    (hs : entrySize (n, v) ≤ t.maxSize) :
    (t.add n v).byAbs t.insertCount = some (n, v) := by
  unfold DynTable.byAbs
  rw [add_entries_fit t n v hs, add_insertCount_fit t n v hs, if_pos (by omega)]
  have hidx : t.insertCount + 1 - 1 - t.insertCount = 0 := by omega
  rw [hidx]
  simp

/-- **`qpack_dyntable_relative_correct` (RFC 9204 §3.2.5 / §4.5.2).** After
inserting `(n, v)`, a field section whose Base is the post-insert `insertCount`
names the just-inserted entry by RELATIVE index 0, and it resolves to EXACTLY
`(n, v)`. -/
theorem qpack_dyntable_relative_correct (t : DynTable) (n v : Bytes)
    (hs : entrySize (n, v) ≤ t.maxSize) :
    (t.add n v).byRelative (t.add n v).insertCount 0 = some (n, v) := by
  unfold DynTable.byRelative
  rw [add_insertCount_fit t n v hs, if_pos (by omega)]
  have hidx : t.insertCount + 1 - 1 - 0 = t.insertCount := by omega
  rw [hidx]
  exact qpack_dyntable_abs_correct t n v hs

/-- **`qpack_dyntable_postbase_correct` (RFC 9204 §3.2.6 / §4.5.3).** After
inserting `(n, v)`, a field section whose Base is the pre-insert `insertCount`
names the just-inserted entry by POST-BASE index 0, and it resolves to EXACTLY
`(n, v)`. -/
theorem qpack_dyntable_postbase_correct (t : DynTable) (n v : Bytes)
    (hs : entrySize (n, v) ≤ t.maxSize) :
    (t.add n v).byPostBase t.insertCount 0 = some (n, v) := by
  unfold DynTable.byPostBase
  have hidx : t.insertCount + 0 = t.insertCount := by omega
  rw [hidx]
  exact qpack_dyntable_abs_correct t n v hs

/-! ## Non-vacuity — a resolver returning nothing is refuted at each index kind -/

theorem qpack_dyntable_abs_refuted (t : DynTable) (n v : Bytes)
    (hs : entrySize (n, v) ≤ t.maxSize) :
    (t.add n v).byAbs t.insertCount ≠ none := by
  rw [qpack_dyntable_abs_correct t n v hs]; exact Option.some_ne_none _

theorem qpack_dyntable_relative_refuted (t : DynTable) (n v : Bytes)
    (hs : entrySize (n, v) ≤ t.maxSize) :
    (t.add n v).byRelative (t.add n v).insertCount 0 ≠ none := by
  rw [qpack_dyntable_relative_correct t n v hs]; exact Option.some_ne_none _

theorem qpack_dyntable_postbase_refuted (t : DynTable) (n v : Bytes)
    (hs : entrySize (n, v) ≤ t.maxSize) :
    (t.add n v).byPostBase t.insertCount 0 ≠ none := by
  rw [qpack_dyntable_postbase_correct t n v hs]; exact Option.some_ne_none _

/-! ## Reduction lemmas for the concrete dynamic-indexed wire vector -/

/-- The 8-bit prefix integer `0x02` (value `2 < 255`) decodes to `2`, no
continuation. -/
theorem decPrefixInt8_two (rest : Bytes) : decPrefixInt 8 0x02 rest = some (2, 0) := by
  unfold decPrefixInt; rfl

/-- The 6-bit prefix integer in `0x80` (`1 0 000000`) decodes to `0`, no
continuation — the relative index of an indexed dynamic field line at index 0. -/
theorem decPrefixInt6_dyn0 : decPrefixInt 6 (0x80 : UInt8) [] = some (0, 0) := by
  decide

/-- §4.5.1.1 reconstruction at the deployed vector: encoded Required Insert
Count 2 against a table with one insert and capacity ≥ 32 reconstructs
Required Insert Count 1 — the general inverse `reconstructRic_correct`
instantiated at `ric = 1`. -/
theorem reconstructRic_two (mx : Nat) (h : 32 ≤ mx) :
    reconstructRic (mx / 32) 1 2 = .ok 1 := by
  have hme : 0 < mx / 32 :=
    (Nat.le_div_iff_mul_le (by omega : 0 < 32)).mpr (by omega)
  have h2 : (1 : Nat) % (2 * (mx / 32)) = 1 := Nat.mod_eq_of_lt (by omega)
  have hcor := reconstructRic_correct (mx / 32) 1 1 hme (by omega) (by omega) (by omega)
  rwa [h2] at hcor

/-! ## The single-line loop step for arbitrary `dyn`/`base` -/

/-- One field line that yields a regular field and then exhausts the input runs
the loop to that single field. -/
theorem decodeLines_single (hd : HuffmanDecoder) (st st' : Store)
    (b : UInt8) (rest : Bytes) (fl : FieldLine) (n : Nat)
    (dyn : DynTable) (base : Nat)
    (hone : decodeOneLine hd st (b :: rest) dyn base = .ok (st', .field fl, n))
    (hdrop : (b :: rest).drop n = []) :
    decodeLines hd st (b :: rest) {} [] dyn base = .ok (st', {}, [fl]) := by
  rw [decodeLines]
  split
  · rename_i e heq; rw [hone] at heq; exact absurd heq (by simp)
  · rename_i st'' out n' heq
    rw [hone] at heq
    simp only [Except.ok.injEq, Prod.mk.injEq] at heq
    obtain ⟨hs, hout, hn⟩ := heq
    subst hs; subst hout; subst hn
    simp only [hdrop]
    rw [decodeLines]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append]

/-! ## Headline theorem 2 — the DEPLOYED decode resolves a dynamic index -/

/-- **`deployed_decodes_dynamic_indexed` (RFC 9204 §4.5.2, indexed dynamic
`T = 0`).** Insert `(n, v)` into a fresh dynamic table (`insertCount = 0`) whose
maximum accommodates it, then run the DEPLOYED `decodeFieldSection` on the wire
bytes `02 00 80` — section prefix (encoded Required Insert Count 1 → Base 1)
followed by an indexed dynamic field line at relative index 0. The decode ACCEPTS,
yields exactly one regular field `⟨ne, ve⟩` and no pseudo-headers, and the decoded
field RESOLVES to EXACTLY the inserted entry: `ne` to `n`, `ve` to `v`.

This is the case the old stub rejected (see `deployed_rejects_dynamic_indexed`).
A resolver that returned no entry fails the acceptance; a resolution to a
different entry fails the byte-equality. Holds for every Huffman-decoder behavior
(the Huffman bit is never set). -/
theorem deployed_decodes_dynamic_indexed (hd : HuffmanDecoder) (t : DynTable)
    (n v : Bytes) (hic0 : t.insertCount = 0)
    (hs : entrySize (n, v) ≤ t.maxSize) (hcap : 32 ≤ t.maxCapacity)
    (hcl : classifyName n = none)
    (hroom : n.length + v.length < sidecarBaseNat) :
    ∃ (r : Decoded) (ne ve : Entry),
      decodeFieldSection hd emptyStore [0x02, 0x00, 0x80] (t.add n v) = .ok r ∧
      r.fields = [⟨ne, ve⟩] ∧ r.pseudo = {} ∧
      r.store.resolve ne = some n.toArray ∧
      r.store.resolve ve = some v.toArray := by
  -- the inserted entry is named by relative index 0 against Base 1
  have hrel : (t.add n v).byRelative 1 0 = some (n, v) := by
    unfold DynTable.byRelative
    rw [if_pos (by omega : (0:Nat) < 1)]
    have hz : (1:Nat) - 1 - 0 = 0 := by omega
    rw [hz]
    have habs := qpack_dyntable_abs_correct t n v hs
    rw [hic0] at habs
    exact habs
  -- the emit of (n, v) succeeds and resolves back to (n, v)
  have hroom' : emptyStore.sidecar.size + n.length + v.length < sidecarBaseNat := by
    show 0 + n.length + v.length < sidecarBaseNat; omega
  obtain ⟨st', ne, ve, hem, hrn, hrv⟩ := emitField_field_ok emptyStore n v hcl hroom'
  -- decode of the single indexed-dynamic line
  have hb80 : ((0x80 : Nat) ≤ (0x80 : UInt8).toNat) = True := eq_true (by decide)
  have hb40 : ((0x40 : Nat) ≤ (0x80 : UInt8).toNat % 0x80) = False := eq_false (by decide)
  have hone : decodeOneLine hd emptyStore [0x80] (t.add n v) 1
      = .ok (st', .field ⟨ne, ve⟩, 1) := by
    unfold decodeOneLine
    simp only [hb80, hb40, reduceIte, decPrefixInt6_dyn0, hrel, hem, Nat.add_zero]
  have hdrop : ([0x80] : Bytes).drop 1 = [] := rfl
  have hlines := decodeLines_single hd emptyStore st' 0x80 [] ⟨ne, ve⟩ 1
    (t.add n v) 1 hone hdrop
  refine ⟨⟨st', {}, [⟨ne, ve⟩]⟩, ne, ve, ?_, rfl, rfl, hrn, hrv⟩
  have hric : reconstructRic (t.maxCapacity / 32) 1 2 = .ok 1 :=
    reconstructRic_two t.maxCapacity hcap
  have hic1 : (t.add n v).insertCount = 1 := by
    rw [add_insertCount_fit t n v hs, hic0]
  unfold decodeFieldSection
  simp only [decPrefixInt8_two, List.drop_zero, decPrefixInt7_zero,
    add_maxCapacity, hic1, hric, reconstructBase_zeroByte, Nat.add_zero,
    Nat.lt_irrefl, reduceIte, hlines]

/-! ## Non-vacuity — the EMPTY-table decode is the refuted stub

Against the default EMPTY table, the same wire shapes the theorem above resolves
still fail — there is nothing to resolve. So the deployed decode occupies exactly
the refuted-stub position when the table is empty, and the populated-table result
above is what closes the gap. -/

/-- One field-line loop step over the single indexed-dynamic byte `0x80`
(`1 T=0 idx=0`) against the EMPTY table hits `dynamicUnsupported`. -/
theorem decodeLines_dynIndexedEmpty (hd : HuffmanDecoder) (st : Store) :
    decodeLines hd st [0x80] {} [] = .error .dynamicUnsupported := by
  have hb80 : ((0x80 : Nat) ≤ (0x80 : UInt8).toNat) = True := eq_true (by decide)
  have hb40 : ((0x40 : Nat) ≤ (0x80 : UInt8).toNat % 0x80) = False := eq_false (by decide)
  have hbr : (DynTable.empty).byRelative 0 0 = (none : Option Pair) := by decide
  have hone : decodeOneLine hd st [0x80] = .error .dynamicUnsupported := by
    unfold decodeOneLine
    simp only [hb80, hb40, reduceIte, decPrefixInt6_dyn0, hbr]
  rw [decodeLines]
  split
  · rename_i e heq; rw [hone] at heq; injection heq with he; rw [← he]
  · rename_i st' out n heq; rw [hone] at heq; exact absurd heq (by simp)

/-- One field-line loop step over the single indexed-post-base byte `0x10`
(`0001 idx=0`) against the EMPTY table hits `dynamicUnsupported`. -/
theorem decodeLines_postBaseEmpty (hd : HuffmanDecoder) (st : Store) :
    decodeLines hd st [0x10] {} [] = .error .dynamicUnsupported := by
  have h80 : ((0x80 : Nat) ≤ (0x10 : UInt8).toNat) = False := eq_false (by decide)
  have h40 : ((0x40 : Nat) ≤ (0x10 : UInt8).toNat) = False := eq_false (by decide)
  have h20 : ((0x20 : Nat) ≤ (0x10 : UInt8).toNat) = False := eq_false (by decide)
  have h10 : ((0x10 : Nat) ≤ (0x10 : UInt8).toNat) = True := eq_true (by decide)
  have hpi : decPrefixInt 4 (0x10 : UInt8) [] = some (0, 0) := by decide
  have hpb : (DynTable.empty).byPostBase 0 0 = (none : Option Pair) := by decide
  have hone : decodeOneLine hd st [0x10] = .error .dynamicUnsupported := by
    unfold decodeOneLine
    simp only [h80, h40, h20, h10, reduceIte, hpi, hpb]
  rw [decodeLines]
  split
  · rename_i e heq; rw [hone] at heq; injection heq with he; rw [← he]
  · rename_i st' out n heq; rw [hone] at heq; exact absurd heq (by simp)

/-- **The DEPLOYED decode rejects a dynamic INDEXED field line against the empty
table.** Prefix `00 00` (Base 0) then `0x80` is rejected with
`Err.dynamicUnsupported` — the refuted-stub position. -/
theorem deployed_rejects_dynamic_indexed (hd : HuffmanDecoder) :
    decodeFieldSection hd emptyStore [0x00, 0x00, 0x80] = .error .dynamicUnsupported := by
  unfold decodeFieldSection
  simp only [decPrefixInt8_zero, List.drop_zero, decPrefixInt7_zero,
    reconstructRic_zero, reconstructBase_zeroByte, Nat.add_zero, Nat.not_lt_zero,
    reduceIte, decodeLines_dynIndexedEmpty]

/-- **The DEPLOYED decode rejects a dynamic POST-BASE field line against the empty
table.** Prefix `00 00` then `0x10` is rejected with `Err.dynamicUnsupported`. -/
theorem deployed_rejects_postbase (hd : HuffmanDecoder) :
    decodeFieldSection hd emptyStore [0x00, 0x00, 0x10] = .error .dynamicUnsupported := by
  unfold decodeFieldSection
  simp only [decPrefixInt8_zero, List.drop_zero, decPrefixInt7_zero,
    reconstructRic_zero, reconstructBase_zeroByte, Nat.add_zero, Nat.not_lt_zero,
    reduceIte, decodeLines_postBaseEmpty]

/-! ## Headline theorem 3 — eviction removes the oldest first -/

/-- **`qpack_dyntable_evict_correct` (RFC 9204 §4.5.1, §3.2.2).** When the incoming
entry `(n, v)` fits the maximum but cannot coexist with everything already stored
(`max < entrySize (n,v) + tableSize pre`), the insert evicts STRICTLY from the OLD
end: the surviving old entries are a proper prefix of the pre-insert table, and the
table is back within its maximum. -/
theorem qpack_dyntable_evict_correct (t : DynTable) (n v : Bytes)
    (hs : entrySize (n, v) ≤ t.maxSize)
    (hfull : t.maxSize < entrySize (n, v) + tableSize t.entries) :
    (t.add n v).entries.tail <+: t.entries ∧
      (t.add n v).entries.tail.length < t.entries.length ∧
      tableSize (t.add n v).entries ≤ t.maxSize := by
  have hadd := add_entries_fit t n v hs
  have htail : (t.add n v).entries.tail
      = keepFit t.entries (t.maxSize - entrySize (n, v)) := by
    rw [hadd]; rfl
  obtain ⟨suf, hsuf⟩ := keepFit_prefix t.entries (t.maxSize - entrySize (n, v))
  have hks := keepFit_size t.entries (t.maxSize - entrySize (n, v))
  have hsuf_ne : suf ≠ [] := by
    intro hnil
    rw [hnil, List.append_nil] at hsuf
    rw [hsuf] at hks
    omega
  have hlen : (keepFit t.entries (t.maxSize - entrySize (n, v))).length
      < t.entries.length := by
    have := congrArg List.length hsuf
    rw [List.length_append] at this
    have hsuflen : 0 < suf.length := List.length_pos.mpr hsuf_ne
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [htail]; exact ⟨suf, hsuf⟩
  · rw [htail]; exact hlen
  · rw [hadd, tableSize_cons]; omega

/-! ## Headline theorem 4 — the encoder-stream Duplicate round trip (§4.3.4) -/

/-- **`qpack_duplicate_abs_correct` (RFC 9204 §4.3.4 + §3.2.4).** When the
deployed encoder-stream executor accepts a Duplicate whose reference resolves
to `(n, v)`, the re-inserted pair is named by absolute index `insertCount`
(the pre-instruction total) and resolves to EXACTLY `(n, v)`. -/
theorem qpack_duplicate_abs_correct (t : DynTable) (idx : Nat) (n v : Bytes)
    (h : t.byRelative t.insertCount idx = some (n, v))
    (hfit : entrySize (n, v) ≤ t.maxSize) (t' : DynTable)
    (hexec : execInstr t (.duplicate idx) = .ok t') :
    t'.byAbs t.insertCount = some (n, v) := by
  rw [execInstr_duplicate_correct t idx n v h hfit] at hexec
  cases hexec
  exact qpack_dyntable_abs_correct t n v hfit

/-! ## Runtime wire vectors (structural definitions, kernel-reducible) -/

-- Entry sizes: e0 = 32 (empty name/value), e1 = e2 = 33 (one-byte name).
private def e0 : Pair := ([], [])          -- size 32
private def e1 : Pair := ([1], [])         -- size 33
private def e2 : Pair := ([2], [])         -- size 33

-- A 70-octet table. e0 then e1 total 32 + 33 = 65 ≤ 70 (both fit); adding e2
-- (size 33) would make 98 > 70, so the oldest, e0, is evicted.
private def t0 : DynTable := ⟨[], 0, 70, 70⟩

private def afterTwo : DynTable := (t0.add e0.1 e0.2).add e1.1 e1.2
private def afterThree : DynTable := afterTwo.add e2.1 e2.2

-- Three inserts ever: the insert count is 3, so absolute indices run 0..2.
#guard afterThree.insertCount == 3

-- The newest entry after three inserts is e2, at absolute index 2 (= insertCount-1).
#guard afterThree.byAbs 2 == some e2

-- e1 (second newest) is at absolute index 1.
#guard afterThree.byAbs 1 == some e1

-- e0 (absolute index 0) was evicted — it no longer resolves.
#guard afterThree.byAbs 0 == none

-- Relative index 0 against Base = insertCount (3) is the newest, e2.
#guard afterThree.byRelative 3 0 == some e2

-- Relative index 1 against Base = 3 is the second newest, e1.
#guard afterThree.byRelative 3 1 == some e1

-- Post-base index 0 against Base = 2 (pre-insert count) names absolute 2 = e2.
#guard afterThree.byPostBase 2 0 == some e2

-- The table is within its maximum after eviction.
#guard decide (tableSize afterThree.entries ≤ afterThree.maxSize)

-- Two entries fit before eviction; three-insert table holds exactly two.
#guard afterTwo.entries.length == 2
#guard afterThree.entries.length == 2

/-! ## Axiom audit -/

#print axioms qpack_dyntable_abs_correct
#print axioms qpack_dyntable_relative_correct
#print axioms qpack_dyntable_postbase_correct
#print axioms qpack_dyntable_add_refines_spec
#print axioms qpack_dyntable_evict_correct
#print axioms deployed_decodes_dynamic_indexed
#print axioms deployed_rejects_dynamic_indexed
#print axioms deployed_rejects_postbase
#print axioms reconstructRic_correct
#print axioms qpack_duplicate_abs_correct
#print axioms execInstr_fits
#print axioms execEncoderStream_fits
#print axioms execInstr_setCapacity_bound
#print axioms execInstr_maxCapacity
#print axioms decodeFieldSection_wf_dyn
#print axioms decPrefixInt_encPrefixInt
#print axioms decDecInstr_encDecInstr

end Qpack
end H3
