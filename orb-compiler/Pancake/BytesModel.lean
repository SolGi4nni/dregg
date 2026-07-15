/-
  Pancake/BytesModel.lean — a BYTE-REGION data-model layer for the translator,
  additive over Pancake/Sem.lean (nothing there is modified).

  THE GAP THIS CLOSES. Sem.lean's `Value := Word` (a 64-bit word) is the only
  data the translator model carries — there is no representation of a `List` of
  bytes as *data*. But the modelled Pancake memory is already byte-addressable
  (`memLoadByte`/`memStoreByte`, transcribed from panSem `mem_load_byte_def` /
  `mem_store_byte_def`). This file adds the missing DATA layer on top: a relation
  `memBytes base len bs s` meaning "the `len` bytes at `base` in `s`'s memory
  equal the Lean byte list `bs : List UInt8`", together with the proven
  load / store / bulk-copy laws over it.

  WHAT IS PROVEN (all `#print axioms`-clean, 0 `sorry`, non-vacuous):
   * The byte-algebra core — `getByte`/`setByte` disjointness
     (`getByte_setByte_same`, `getByte_setByte_diff`) and address injectivity
     (`addr_eq_of_align_index`) — from which the memory laws follow.
   * `memBytes_load`  : a `LoadByte` at `base + i` reads exactly `bs[i]`.
   * `memBytes_store` : a byte-store at `base + i` updates the region to
     `bs.set i b`, disturbing no other byte (the packed-region law).
   * `writeByteArray_memBytes` / `writeByteArray_preserves` : a BOUNDED byte
     copy (`write_bytearray`, the model's bulk byte-store) establishes `memBytes`
     on the destination and preserves any disjoint region.

  This is the model layer only. NO machine-code claims here.
-/
import Pancake.Sem

namespace Pancake.BytesModel

open Pancake

variable {σ : Type}

/-! ## 1. Low-bit mask lemma -/

/-- Low-bit mask `(1 <<< n) - 1` has bit `j` set iff `j < n`, for `j < 64`, `n ≤ 64`. -/
theorem getLsbD_lowMask {n j : Nat} (hn : n ≤ 64) (hj : j < 64) :
    ((1#64 <<< n) - 1#64).getLsbD j = decide (j < n) := by
  rcases Nat.lt_or_eq_of_le hn with hlt | heq
  · have hpow : (2:Nat) ^ n < 2 ^ 64 := Nat.pow_lt_pow_right (by omega : 1 < 2) hlt
    have h1 : (1:Nat) ≤ 2 ^ n := Nat.one_le_two_pow
    have hval : ((1#64 <<< n) - 1#64) = BitVec.ofNat 64 (2 ^ n - 1) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
                 Nat.one_mul]
      generalize hp : (2:Nat) ^ n = p at *
      omega
    rw [hval, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
    simp only [hj, decide_true, Bool.true_and]
  · subst heq
    have hval : ((1#64 <<< 64) - 1#64) = BitVec.allOnes 64 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_allOnes,
                 Nat.shiftLeft_eq]
    rw [hval, BitVec.getLsbD_allOnes]

/-! ## 2. Byte-position facts -/

/-- `byteIndex a be` is at most 56 (a byte position, multiple of 8 in `[0,56]`). -/
theorem byteIndex_le (a : Word) (be : Bool) : byteIndex a be ≤ 56 := by
  have h : a.toNat % 8 < 8 := Nat.mod_lt _ (by omega)
  simp only [byteIndex]
  split <;> omega

/-- `byteIndex a be` is a multiple of 8. -/
theorem byteIndex_dvd (a : Word) (be : Bool) : 8 ∣ byteIndex a be := by
  simp only [byteIndex]
  split <;> exact ⟨_, rfl⟩

/-! ## 3. The `getByte`/`setByte` disjointness algebra (the faithfulness core) -/

/-- GET after SET at the SAME byte position recovers the stored byte. -/
theorem getByte_setByte_same (a : Word) (b : BitVec 8) (w : Word) (be : Bool) :
    getByte a (setByte a b w be) be = b := by
  have hi : byteIndex a be ≤ 56 := byteIndex_le a be
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro j hj
  simp only [getByte, setByte, wordSliceAlt, BitVec.getLsbD_setWidth,
             BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_and,
             BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  generalize hidef : byteIndex a be = i at hi ⊢
  have hij64 : i + j < 64 := by omega
  have hsub : i + j - i = j := by omega
  have d2 : ¬ (i + j < i) := by omega
  have d3 : (i + j < i + 8) := by omega
  have d4 : ¬ (i + j < 0) := by omega
  have d5 : (j < 64) := by omega
  rw [getLsbD_lowMask (show (64:Nat) ≤ 64 by omega) hij64,
      getLsbD_lowMask (show i + 8 ≤ 64 by omega) hij64,
      getLsbD_lowMask (show i ≤ 64 by omega) hij64,
      getLsbD_lowMask (show (0:Nat) ≤ 64 by omega) hij64]
  simp only [hsub, hij64, d2, d3, d4, d5, hj, decide_true, decide_false,
             Bool.true_and, Bool.and_true, Bool.false_and, Bool.and_false,
             Bool.not_true, Bool.not_false, Bool.or_false, Bool.false_or, Bool.or_true]

/-- GET after SET at a DIFFERENT byte position leaves the read byte unchanged. -/
theorem getByte_setByte_diff (a a' : Word) (b : BitVec 8) (w : Word) (be : Bool)
    (hne : byteIndex a be ≠ byteIndex a' be) :
    getByte a (setByte a' b w be) be = getByte a w be := by
  have hi : byteIndex a be ≤ 56 := byteIndex_le a be
  have hi' : byteIndex a' be ≤ 56 := byteIndex_le a' be
  have hd : 8 ∣ byteIndex a be := byteIndex_dvd a be
  have hd' : 8 ∣ byteIndex a' be := byteIndex_dvd a' be
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro j hj
  simp only [getByte, setByte, wordSliceAlt, BitVec.getLsbD_setWidth,
             BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_and,
             BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft]
  generalize hidef : byteIndex a be = i at hi hd hne ⊢
  generalize hidef' : byteIndex a' be = i' at hi' hd' hne ⊢
  have hij64 : i + j < 64 := by omega
  rw [getLsbD_lowMask (show (64:Nat) ≤ 64 by omega) hij64,
      getLsbD_lowMask (show i' + 8 ≤ 64 by omega) hij64,
      getLsbD_lowMask (show i' ≤ 64 by omega) hij64,
      getLsbD_lowMask (show (0:Nat) ≤ 64 by omega) hij64]
  rcases (show i + 8 ≤ i' ∨ i' + 8 ≤ i by omega) with h | h
  · have c1 : (i + j < i') := by omega
    have c2 : (i + j < i' + 8) := by omega
    have c3 : ¬ (i + j < 0) := by omega
    simp only [hij64, c1, c2, c3, hj, decide_true, decide_false,
               Bool.true_and, Bool.and_true, Bool.false_and, Bool.and_false,
               Bool.not_true, Bool.not_false, Bool.or_false, Bool.false_or, Bool.or_true]
  · have c1 : ¬ (i + j < i') := by omega
    have c2 : ¬ (i + j < i' + 8) := by omega
    have c3 : ¬ (i + j < 0) := by omega
    have hb0 : b.getLsbD (i + j - i') = false := by apply BitVec.getLsbD_of_ge; omega
    simp only [hij64, c1, c2, c3, hb0, hj, decide_true, decide_false,
               Bool.true_and, Bool.and_true, Bool.false_and, Bool.and_false,
               Bool.not_true, Bool.not_false, Bool.or_false, Bool.false_or, Bool.or_true]

/-! ## 4. Address injectivity: align + byte-index pin the address -/

/-- On the high bits (`k ≥ 3`), `byteAlign` is transparent. -/
theorem getLsbD_byteAlign_high (w : Word) (k : Nat) (h3 : 3 ≤ k) (hk : k < 64) :
    (byteAlign w).getLsbD k = w.getLsbD k := by
  simp only [byteAlign, BitVec.getLsbD_and, BitVec.getLsbD_not]
  have h7 : (7 : Word).getLsbD k = false := by
    rw [show (7 : Word) = BitVec.ofNat 64 7 from rfl, BitVec.getLsbD_ofNat,
        show (7:Nat) = 2 ^ 3 - 1 from rfl, Nat.testBit_two_pow_sub_one]
    simp [Nat.not_lt.mpr h3]
  rw [h7]; simp [hk]

/-- On the low bits (`k < 3`), equal `mod 8` gives equal bit. -/
theorem getLsbD_low_of_mod (w w' : Word) (hmod : w.toNat % 8 = w'.toNat % 8)
    (k : Nat) (h3 : k < 3) : w.getLsbD k = w'.getLsbD k := by
  have e : ∀ x : Nat, x.testBit k = (x % 8).testBit k := by
    intro x; rw [show (8:Nat) = 2 ^ 3 from rfl, Nat.testBit_mod_two_pow]; simp [h3]
  simp only [BitVec.getLsbD]
  rw [e w.toNat, e w'.toNat, hmod]

/-- ADDRESS INJECTIVITY: two addresses with the same aligned word and the same
byte index are equal. This is what makes the packed-region store law hold. -/
theorem addr_eq_of_align_index (w w' : Word) (be : Bool)
    (ha : byteAlign w = byteAlign w') (hib : byteIndex w be = byteIndex w' be) : w = w' := by
  have hmod : w.toNat % 8 = w'.toNat % 8 := by
    have h8 : w.toNat % 8 < 8 := Nat.mod_lt _ (by omega)
    have h8' : w'.toNat % 8 < 8 := Nat.mod_lt _ (by omega)
    cases be <;> simp [byteIndex] at hib <;> omega
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro k hk
  rcases Nat.lt_or_ge k 3 with h3 | h3
  · exact getLsbD_low_of_mod w w' hmod k h3
  · rw [← getLsbD_byteAlign_high w k h3 hk, ← getLsbD_byteAlign_high w' k h3 hk, ha]

/-! ## 5. The memory-level store/load laws -/

/-- The memory after a single byte-store (the `some` branch of `mem_store_byte`). -/
def putByte (m : Word → Word) (be : Bool) (w : Word) (b : BitVec 8) : Word → Word :=
  fun k => if k = byteAlign w then setByte w b (m (byteAlign w)) be else m k

/-- `mem_store_byte` succeeds (into `putByte`) exactly when the aligned word is in range. -/
theorem memStore_eq (m : Word → Word) (dm : Word → Bool) (be : Bool) (w : Word) (b : BitVec 8)
    (h : dm (byteAlign w) = true) :
    memStoreByte m dm be w b = some (putByte m be w b) := by
  unfold memStoreByte putByte
  rw [if_pos h]

/-- LOAD after STORE at the SAME address reads the stored byte. -/
theorem load_putByte_same (m : Word → Word) (dm : Word → Bool) (be : Bool)
    (w : Word) (b : BitVec 8) (h : dm (byteAlign w) = true) :
    memLoadByte (putByte m be w b) dm be w = some b := by
  have hinner : (putByte m be w b) (byteAlign w) = setByte w b (m (byteAlign w)) be := by
    simp only [putByte, if_true]
  simp only [memLoadByte, hinner, getByte_setByte_same, h, if_true]

/-- LOAD after STORE at a DIFFERENT address is undisturbed. -/
theorem load_putByte_diff (m : Word → Word) (dm : Word → Bool) (be : Bool)
    (w : Word) (b : BitVec 8) (w' : Word) (hw : w' ≠ w) :
    memLoadByte (putByte m be w b) dm be w' = memLoadByte m dm be w' := by
  have hX : getByte w' ((putByte m be w b) (byteAlign w')) be
          = getByte w' (m (byteAlign w')) be := by
    simp only [putByte]
    by_cases hba : byteAlign w' = byteAlign w
    · rw [if_pos hba]
      have hidx : byteIndex w' be ≠ byteIndex w be :=
        fun hii => hw (addr_eq_of_align_index w' w be hba hii)
      rw [getByte_setByte_diff w' w b (m (byteAlign w)) be hidx, hba]
    · rw [if_neg hba]
  simp only [memLoadByte, hX]

/-! ## 6. `memBytes`: a byte region as a relation on the model memory

`memBytes base len bs s` : the `len = bs.length` bytes at `base` in `s`'s memory
equal the Lean byte list `bs : List UInt8`. `len : Word` frames it as a
base-pointer + length region (the standard flat lowering). -/
def memBytes (base len : Word) (bs : List UInt8) (s : PancakeState σ) : Prop :=
  bs.length = len.toNat ∧
  ∀ i (h : i < bs.length),
    memLoadByte s.memory s.memaddrs s.be (base + BitVec.ofNat 64 i) = some (bs[i].toBitVec)

/-- Address injectivity across the region: distinct in-range byte offsets give
distinct addresses (`len < 2^64`, the only ambient size side-condition). -/
theorem region_addr_inj (base : Word) (i j : Nat) (hi : i < 2 ^ 64) (hj : j < 2 ^ 64)
    (hne : i ≠ j) : base + BitVec.ofNat 64 i ≠ base + BitVec.ofNat 64 j := by
  intro hEq
  rw [BitVec.add_right_inj] at hEq
  apply hne
  have := congrArg BitVec.toNat hEq
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using this

/-! ## 7. LOAD law: a `LoadByte` at `base + i` reads `bs[i]`. -/

theorem memBytes_load (base len : Word) (bs : List UInt8) (s : PancakeState σ)
    (hmb : memBytes base len bs s) (i : Nat) (hi : i < bs.length) (e : PancakeExp)
    (he : eval s e = some (base + BitVec.ofNat 64 i)) :
    eval s (.loadByte e) = some ((bs[i].toBitVec).setWidth 64) := by
  simp only [eval, he, hmb.2 i hi]

/-! ## 8. STORE law: a byte-store at `base + i` updates the region to `bs.set i b`. -/

theorem memBytes_store (base len : Word) (bs : List UInt8) (s : PancakeState σ)
    (hlen : len.toNat < 2 ^ 64) (hmb : memBytes base len bs s)
    (i : Nat) (hi : i < bs.length) (b : UInt8) :
    memBytes base len (bs.set i b)
      { s with memory := putByte s.memory s.be (base + BitVec.ofNat 64 i) b.toBitVec } := by
  obtain ⟨hlenEq, hbytes⟩ := hmb
  have hdm : s.memaddrs (byteAlign (base + BitVec.ofNat 64 i)) = true := by
    have hx := hbytes i hi
    unfold memLoadByte at hx
    by_cases hd : s.memaddrs (byteAlign (base + BitVec.ofNat 64 i)) = true
    · exact hd
    · rw [if_neg hd] at hx; exact absurd hx (by simp)
  refine ⟨by rw [List.length_set]; exact hlenEq, ?_⟩
  intro j hj
  have hjlen : j < bs.length := by rwa [List.length_set] at hj
  have hilt64 : i < 2 ^ 64 := by rw [hlenEq] at hi; omega
  have hjlt64 : j < 2 ^ 64 := by rw [hlenEq] at hjlen; omega
  by_cases hij : j = i
  · subst hij
    have hz : memLoadByte (putByte s.memory s.be (base + BitVec.ofNat 64 j) b.toBitVec)
              s.memaddrs s.be (base + BitVec.ofNat 64 j) = some b.toBitVec :=
      load_putByte_same s.memory s.memaddrs s.be (base + BitVec.ofNat 64 j) b.toBitVec hdm
    rw [List.getElem_set_self]
    exact hz
  · have hAddr : base + BitVec.ofNat 64 j ≠ base + BitVec.ofNat 64 i :=
      region_addr_inj base j i hjlt64 hilt64 hij
    have hpres := load_putByte_diff s.memory s.memaddrs s.be
                    (base + BitVec.ofNat 64 i) b.toBitVec (base + BitVec.ofNat 64 j) hAddr
    have hbj := hbytes j hjlen
    rw [List.getElem_set_ne (Ne.symm hij), hpres, hbj]

/-! ## 9. A BOUNDED byte copy via `write_bytearray` (the model's bulk byte-store)

The model's programmatic byte-store surface is `write_bytearray` (panSem
`write_bytearray_def`), the memory transformer an `ExtCall` uses to write bytes
back into an array. It is a bounded, structurally-recursive loop over the byte
list. Here we prove the two memcpy laws: writing a byte vector ESTABLISHES
`memBytes` on the destination, and PRESERVES any disjoint region. -/

/-- `ofNat (j+1) = ofNat j + 1`. -/
theorem ofNat_succ (j : Nat) : BitVec.ofNat 64 (j + 1) = BitVec.ofNat 64 j + 1#64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- One step of the address walk: `base + (j+1) = (base+1) + j`. -/
theorem addr_succ (base : Word) (j : Nat) :
    base + BitVec.ofNat 64 (j + 1) = (base + 1) + BitVec.ofNat 64 j := by
  rw [ofNat_succ, BitVec.add_comm (BitVec.ofNat 64 j) (1#64), ← BitVec.add_assoc]
  rfl

/-- PRESERVE: a byte outside the written region `[base, base+len)` is undisturbed
by `write_bytearray`. -/
theorem writeByteArray_preserves (dm : Word → Bool) (be : Bool) (bs : List (BitVec 8)) (w : Word) :
    ∀ (base : Word) (m : Word → Word),
      (∀ j, j < bs.length → w ≠ base + BitVec.ofNat 64 j) →
      memLoadByte (writeByteArray dm be base bs m) dm be w = memLoadByte m dm be w := by
  induction bs with
  | nil => intro base m _; rfl
  | cons b bs ih =>
    intro base m hout
    have hne0 : w ≠ base := by have := hout 0 (by simp); simpa using this
    have htail : memLoadByte (writeByteArray dm be (base + 1) bs m) dm be w = memLoadByte m dm be w := by
      apply ih (base + 1) m
      intro j hj
      have := hout (j + 1) (by simp only [List.length_cons]; omega)
      rwa [addr_succ base j] at this
    have hstep : memLoadByte (writeByteArray dm be base (b :: bs) m) dm be w
               = memLoadByte (writeByteArray dm be (base + 1) bs m) dm be w := by
      simp only [writeByteArray]
      by_cases hdmb : dm (byteAlign base) = true
      · rw [memStore_eq _ dm be base b hdmb, load_putByte_diff _ dm be base b w hne0]
      · have hnone : memStoreByte (writeByteArray dm be (base + 1) bs m) dm be base b = none := by
          unfold memStoreByte; rw [if_neg hdmb]
        rw [hnone]
    rw [hstep, htail]

/-- ESTABLISH (over `List (BitVec 8)`): after `write_bytearray`, reading `base + j`
returns `bs[j]`, provided every written aligned word is in range. -/
theorem writeByteArray_memBytes (dm : Word → Bool) (be : Bool) (bs : List (BitVec 8)) :
    ∀ (base : Word) (m : Word → Word),
      bs.length < 2 ^ 64 →
      (∀ k, k < bs.length → dm (byteAlign (base + BitVec.ofNat 64 k)) = true) →
      ∀ j (hj : j < bs.length),
        memLoadByte (writeByteArray dm be base bs m) dm be (base + BitVec.ofNat 64 j) = some bs[j] := by
  induction bs with
  | nil => intro base m _ _ j hj; exact absurd hj (by simp)
  | cons b bs ih =>
    intro base m hlen hdm j hj
    simp only [List.length_cons] at hlen
    have hdm0 : dm (byteAlign base) = true := by have := hdm 0 (by simp); simpa using this
    have hstep : writeByteArray dm be base (b :: bs) m
               = putByte (writeByteArray dm be (base + 1) bs m) be base b := by
      simp only [writeByteArray]; rw [memStore_eq _ dm be base b hdm0]
    rw [hstep]
    cases j with
    | zero =>
      rw [show base + BitVec.ofNat 64 0 = base by simp, load_putByte_same _ dm be base b hdm0]
      rfl
    | succ j =>
      have hjb : j < bs.length := by simp only [List.length_cons] at hj; omega
      have hne : base + BitVec.ofNat 64 (j + 1) ≠ base := by
        have hk := region_addr_inj base (j + 1) 0 (by omega) (by omega) (by omega)
        simpa using hk
      rw [load_putByte_diff _ dm be base b (base + BitVec.ofNat 64 (j + 1)) hne, addr_succ base j]
      have hih := ih (base + 1) m (by omega)
        (fun k hk => by
          have := hdm (k + 1) (by simp only [List.length_cons]; omega)
          rwa [addr_succ base k] at this) j hjb
      rw [hih]; rfl

/-- The memcpy ESTABLISH law in region vocabulary: writing the byte vector `bs`
(a `List UInt8`, the Lean serve payload) to `base` makes `memBytes` hold there. -/
theorem memBytes_of_write (base len : Word) (bs : List UInt8) (s : PancakeState σ)
    (hlenEq : bs.length = len.toNat) (hlen : len.toNat < 2 ^ 64)
    (hdm : ∀ k, k < bs.length → s.memaddrs (byteAlign (base + BitVec.ofNat 64 k)) = true) :
    memBytes base len bs
      { s with memory := writeByteArray s.memaddrs s.be base (bs.map (·.toBitVec)) s.memory } := by
  refine ⟨hlenEq, ?_⟩
  intro j hj
  have hjm : j < (bs.map (·.toBitVec)).length := by simpa using hj
  have hcore := writeByteArray_memBytes s.memaddrs s.be (bs.map (·.toBitVec)) base s.memory
    (by simpa using (by omega : bs.length < 2 ^ 64))
    (fun k hk => by simp only [List.length_map] at hk; exact hdm k hk) j hjm
  show memLoadByte (writeByteArray s.memaddrs s.be base (bs.map (·.toBitVec)) s.memory)
        s.memaddrs s.be (base + BitVec.ofNat 64 j) = _
  rw [hcore]
  simp

end Pancake.BytesModel
