/-
  Pancake/LowerBridgeSem.lean — the SEMANTIC half of the PStmt ⟷ PancakeProg bridge
  (the byte-store landing lemma). Companion to LowerBridge.lean, which closed the
  SYNTACTIC half. DreggNet-only; owns a disjoint file (edits nothing else).

  GROUND (LowerBridge.lean). `storesIntoL_lowers` / `storesInto_lowers` relate the
  EMITTED per-byte `st8` head `storesInto dst bs` (the DSL the pretty-printer turns
  into `.pnk`) to a named model `.storeByte` program `storesModel dst ((range|bs|).zip bs)`
  via the parse-faithful `lower`. That is emitted-syntax ⟷ model-program; it does NOT
  say the model program LANDS the right bytes. LowerBridge §4 named the blocker: `st8`
  runs `mem_store_byte` = `byteAlign`+`setByte` (one byte per ADDRESS, sub-word packing),
  NOT one-byte-per-WORD like `MemBytesAt`/`storeLit_membytes`. So a byte-ADDRESSED post
  state and landing lemma were required, and left open.

  WHAT THIS FILE PROVES (the semantic half, byte-addressed).

   * `MemBytesAtB m dm be base bs` — the byte-addressed region predicate: reading byte
     `i` at consecutive byte address `base + i` via the faithful `mem_load_byte`
     (`memLoadByte`, the exact primitive `LoadByte` evaluates) returns `bs[i]`. This is
     the `storeByte`-flavoured analogue of the word-addressed `MemBytesAt`.

   * `storesModel_landsB` — running the model `storeByte` program lands `bs`
     byte-addressed at `base`, for ALL byte lists, EVEN where consecutive bytes pack
     into one 64-bit word. The packing case is what `MemBytesAt` cannot express and is
     the real content: it rests on get_byte/set_byte NON-INTERFERENCE, proved here from
     the CakeML `byteScript` definitions (`getByteAt_setByteAt_ne` + `byteAlign_byteIndex_inj`:
     distinct byte addresses in one word have distinct byte indices).

   * `serve_head_landsB` — END-TO-END head correctness: the EMITTED head lowers
     (syntactic, from LowerBridge) to a named `P`, and running `P` lands the bytes
     byte-addressed (semantic). Emitted-syntax to landed-bytes, closed.

  Nothing in Pancake/Sem was found missing: the byte-addressed model is `memLoadByte`
  ∘ `memStoreByte`, both already transcribed from panSem. No new named assumption.

  AXIOM FOOTPRINT: ⊆ {propext, Classical.choice, Quot.sound}, 0 sorryAx, no bv_decide
  native axiom (the non-interference is a hand getLsbD/testBit proof). Built per-file
  against the prebuilt olean set, the same pattern as LowerBridge.lean.
-/
import Pancake.LowerBridge

namespace Pancake.LowerBridgeSem
open Pancake
open Pancake.LowerBridge (addrModel storesModel)
open Pancake.ServeEmit (storesInto)
open Pancake.Lower (lowerStmtsFold)

variable {σ : Type}



theorem maskLsbD (n k : Nat) (hn : n ≤ 64) (hk : k < 64) :
    ((1#64 <<< n) - 1#64).getLsbD k = decide (k < n) := by
  have hmaskEq : (1#64 <<< n) - 1#64 = BitVec.setWidth 64 (BitVec.allOnes n) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_allOnes]
    simp only [BitVec.toNat_ofNat]
    have h1 : (1:Nat) % 2^64 = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
    have hlo : (1:Nat) ≤ 2^n := Nat.one_le_two_pow
    have hpow : (2:Nat)^n ≤ 2^64 := Nat.pow_le_pow_right (by omega) hn
    rw [h1, Nat.one_shiftLeft]
    rcases Nat.lt_or_ge n 64 with h | h
    · have hlt : (2:Nat)^n < 2^64 := Nat.pow_lt_pow_right (by omega) h
      rw [Nat.mod_eq_of_lt hlt]; omega
    · have : n = 64 := by omega
      subst this; omega
  rw [hmaskEq, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes]
  simp [hk]

/-- getLsbD of `wordSliceAlt`: keep bits `[lo, hi)` of `w`. -/
theorem wordSliceAlt_getLsbD (hi lo : Nat) (w : Word) (j : Nat)
    (hhi : hi ≤ 64) (hlo : lo ≤ 64) (hj : j < 64) :
    (wordSliceAlt hi lo w).getLsbD j
      = (w.getLsbD j && decide (j < hi) && !decide (j < lo)) := by
  unfold wordSliceAlt
  rw [BitVec.getLsbD_and, BitVec.getLsbD_and, BitVec.getLsbD_not,
      maskLsbD hi j hhi hj, maskLsbD lo j hlo hj]
  simp only [hj, decide_true, Bool.true_and, Bool.and_assoc]

/-- Byte at word-bit position `i`. -/
def getByteAt (i : Nat) (w : Word) : BitVec 8 := (w >>> i).setWidth 8

/-- Overwrite the 8 bits at word-bit position `i` with `b`. -/
def setByteAt (i : Nat) (b : BitVec 8) (w : Word) : Word :=
  wordSliceAlt 64 (i + 8) w ||| ((b.setWidth 64) <<< i) ||| wordSliceAlt i 0 w

/-- getLsbD of a byte read: bit `k` of the byte = bit `i+k` of the word. -/
theorem getByteAt_getLsbD (i k : Nat) (hi : i + 8 ≤ 64) (hk : k < 8) (w : Word) :
    (getByteAt i w).getLsbD k = w.getLsbD (i + k) := by
  unfold getByteAt
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  rw [Nat.add_comm i k]
  simp [hk]




theorem getByteAt_setByteAt_same (i : Nat) (hi : i + 8 ≤ 64) (b : BitVec 8) (w : Word) :
    getByteAt i (setByteAt i b w) = b := by
  rw [BitVec.eq_of_getLsbD_eq_iff]
  intro k hk
  rw [getByteAt_getLsbD i k hi hk]
  unfold setByteAt
  rw [BitVec.getLsbD_or, BitVec.getLsbD_or,
      wordSliceAlt_getLsbD 64 (i+8) w (i+k) (by omega) (by omega) (by omega),
      wordSliceAlt_getLsbD i 0 w (i+k) (by omega) (by omega) (by omega),
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  have e2 : (i + k < i + 8) := by omega
  have e1 : ¬ (i + k < i) := by omega
  have e3 : (i + k < 64) := by omega
  have e4 : (k < 64) := by omega
  have e5 : i + k - i = k := by omega
  simp [e1, e2, e3, e4, e5]

theorem getByteAt_setByteAt_ne (i i' : Nat) (hi : i + 8 ≤ 64) (hi' : i' + 8 ≤ 64)
    (hi8 : i % 8 = 0) (hi'8 : i' % 8 = 0) (hne : i ≠ i') (b : BitVec 8) (w : Word) :
    getByteAt i (setByteAt i' b w) = getByteAt i w := by
  rw [BitVec.eq_of_getLsbD_eq_iff]
  intro k hk
  rw [getByteAt_getLsbD i k hi hk, getByteAt_getLsbD i k hi hk]
  unfold setByteAt
  rw [BitVec.getLsbD_or, BitVec.getLsbD_or,
      wordSliceAlt_getLsbD 64 (i'+8) w (i+k) (by omega) (by omega) (by omega),
      wordSliceAlt_getLsbD i' 0 w (i+k) (by omega) (by omega) (by omega),
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  -- i, i' are distinct multiples of 8 ⇒ |i - i'| ≥ 8
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · -- i < i' ⇒ i + 8 ≤ i' ⇒ i+k < i'
    have e1 : (i + k < i' + 8) := by omega
    have e2 : (i + k < i') := by omega
    simp [e1, e2]
  · -- i > i' ⇒ i ≥ i' + 8 ⇒ i+k ≥ i'+8
    have e1 : ¬ (i + k < i' + 8) := by omega
    have e2 : ¬ (i + k < i') := by omega
    have e3 : (i + k < 64) := by omega
    have eb : b.getLsbD (i + k - i') = false := BitVec.getLsbD_of_ge b (i + k - i') (by omega)
    simp [e1, e2, e3, eb]




/-- `getLsbD` of any `Word` whose `toNat` is `7` (the low-3-bit mask), form-agnostic
so it matches both the `7#64` and `(7 : Word)` numeral spellings. -/
theorem getLsbD_toNat7 (w7 : Word) (h : w7.toNat = 7) (j : Nat) :
    w7.getLsbD j = decide (j < 3) := by
  show w7.toNat.testBit j = decide (j < 3)
  rw [h, show (7:Nat) = 2^3 - 1 from rfl, Nat.testBit_two_pow_sub_one]

theorem byteIndex_lt (a : Word) (be : Bool) : byteIndex a be + 8 ≤ 64 := by
  have h : a.toNat % 8 < 8 := Nat.mod_lt _ (by omega)
  cases be <;> simp only [byteIndex, Bool.false_eq_true, if_false, if_true] <;> omega

theorem byteIndex_mod8 (a : Word) (be : Bool) : byteIndex a be % 8 = 0 := by
  cases be <;> simp only [byteIndex, Bool.false_eq_true, if_false, if_true] <;> omega

theorem mod8_eq_and (a : Word) : a.toNat % 8 = (a &&& 7#64).toNat := by
  rw [BitVec.toNat_and]
  have h7 : (7#64).toNat = 2^3 - 1 := by decide
  rw [h7, Nat.and_two_pow_sub_one_eq_mod]

theorem byteAlign_byteIndex_inj (a a' : Word) (be : Bool)
    (hal : byteAlign a = byteAlign a') (hidx : byteIndex a be = byteIndex a' be) : a = a' := by
  have hlow : a &&& 7#64 = a' &&& 7#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [← mod8_eq_and, ← mod8_eq_and]
    have ha : a.toNat % 8 < 8 := Nat.mod_lt _ (by omega)
    have ha' : a'.toNat % 8 < 8 := Nat.mod_lt _ (by omega)
    cases be <;>
      simp only [byteIndex, Bool.false_eq_true, if_false, if_true] at hidx <;> omega
  unfold byteAlign at hal
  rw [BitVec.eq_of_getLsbD_eq_iff]
  intro j hj
  by_cases hj3 : j < 3
  · have hsev : (7#64).getLsbD j = true := by
      rw [getLsbD_toNat7 (7#64) (by decide) j]; simp [hj3]
    have hb := congrArg (fun x => x.getLsbD j) hlow
    simp only [BitVec.getLsbD_and, hsev, Bool.and_true] at hb
    exact hb
  · have hnot : (~~~(7 : Word)).getLsbD j = true := by
      rw [BitVec.getLsbD_not, getLsbD_toNat7 (7 : Word) (by decide) j]; simp [hj, hj3]
    have hb := congrArg (fun x => x.getLsbD j) hal
    simp only [BitVec.getLsbD_and, hnot, Bool.and_true] at hb
    exact hb

theorem byteIndex_ne (a a' : Word) (be : Bool)
    (hal : byteAlign a = byteAlign a') (hne : a ≠ a') :
    byteIndex a be ≠ byteIndex a' be :=
  fun hidx => hne (byteAlign_byteIndex_inj a a' be hal hidx)




/-! ## getByte/setByte bridge (from the byte-slice At-lemmas) -/

theorem getByte_setByte_same (a : Word) (b : BitVec 8) (w : Word) (be : Bool) :
    getByte a (setByte a b w be) be = b :=
  getByteAt_setByteAt_same (byteIndex a be) (byteIndex_lt a be) b w

theorem getByte_setByte_ne (a a' : Word) (b : BitVec 8) (w : Word) (be : Bool)
    (hal : byteAlign a = byteAlign a') (hne : a ≠ a') :
    getByte a (setByte a' b w be) be = getByte a w be :=
  getByteAt_setByteAt_ne (byteIndex a be) (byteIndex a' be)
    (byteIndex_lt a be) (byteIndex_lt a' be) (byteIndex_mod8 a be) (byteIndex_mod8 a' be)
    (byteIndex_ne a a' be hal hne) b w

/-! ## eval of the emitted store address -/

theorem eval_addrModel {σ : Type} (s : PancakeState σ) (dst : String) (base : Word) (k : Nat)
    (hbase : s.locals dst = some base) :
    eval s (addrModel dst k) = some (base + BitVec.ofNat 64 k) := by
  unfold addrModel
  by_cases hk : k = 0
  · subst hk
    simp only [beq_self_eq_true, if_true]
    show s.locals dst = some (base + BitVec.ofNat 64 0)
    rw [hbase]; simp
  · rw [if_neg (by simpa using hk)]
    show (match eval s (.var dst), eval s (.const (BitVec.ofNat 64 k)) with
          | some a, some b => some (a + b) | _, _ => none) = _
    simp only [eval, hbase]

/-! ## the byte-store post-state and its read-back -/


/-- The memory after one `st8 adr := bt`: overwrite byte at `adr`, keep the rest. -/
def afterStore (s : PancakeState σ) (adr : Word) (bt : BitVec 8) : PancakeState σ :=
  { s with memory := fun k =>
      if k = byteAlign adr then setByte adr bt (s.memory (byteAlign adr)) s.be else s.memory k }

/-- Running one emitted byte store from a state whose `dst` holds `base` lands `afterStore`. -/
theorem run_headStore (o : Oracle σ) (s : PancakeState σ) (dst : String) (base : Word)
    (k b : Nat) (hbase : s.locals dst = some base)
    (haddr : s.memaddrs (byteAlign (base + BitVec.ofNat 64 k)) = true) :
    PancakeSem o (.storeByte (addrModel dst k) (.const (BitVec.ofNat 64 b))) s
      = (none, afterStore s (base + BitVec.ofNat 64 k) ((BitVec.ofNat 64 b).setWidth 8)) := by
  have hd : eval s (addrModel dst k) = some (base + BitVec.ofNat 64 k) :=
    eval_addrModel s dst base k hbase
  have hs : eval s (.const (BitVec.ofNat 64 b)) = some (BitVec.ofNat 64 b) := rfl
  have hm : memStoreByte s.memory s.memaddrs s.be (base + BitVec.ofNat 64 k)
              ((BitVec.ofNat 64 b).setWidth 8)
            = some (afterStore s (base + BitVec.ofNat 64 k) ((BitVec.ofNat 64 b).setWidth 8)).memory := by
    unfold memStoreByte afterStore
    rw [if_pos haddr]
  rw [evaluate_storeByte o s hd hs hm]
  rfl

/-! ## read-back of the stored byte, and non-interference for other addresses -/

theorem load_afterStore_same (s : PancakeState σ) (adr : Word) (bt : BitVec 8)
    (haddr : s.memaddrs (byteAlign adr) = true) :
    memLoadByte (afterStore s adr bt).memory s.memaddrs s.be adr = some bt := by
  unfold memLoadByte afterStore
  rw [if_pos haddr]
  simp only [if_true]
  rw [getByte_setByte_same]

theorem load_afterStore_ne (s : PancakeState σ) (adr adr' : Word) (bt : BitVec 8)
    (hne : adr' ≠ adr) :
    memLoadByte (afterStore s adr bt).memory s.memaddrs s.be adr'
      = memLoadByte s.memory s.memaddrs s.be adr' := by
  unfold memLoadByte afterStore
  by_cases hcell : byteAlign adr' = byteAlign adr
  · rw [hcell]
    simp only [if_true]
    by_cases hdm : s.memaddrs (byteAlign adr) = true
    · rw [if_pos hdm, if_pos hdm]
      rw [getByte_setByte_ne adr' adr bt _ s.be hcell hne]
    · rw [if_neg hdm, if_neg hdm]
  · simp only [if_neg hcell]





theorem sem_seq_none' (o : Oracle σ) {c1 c2 : PancakeProg} {s s1 s' : PancakeState σ}
    (h1 : PancakeSem o c1 s = (none, s1)) (hclk : s1.clock = s.clock)
    (h2 : PancakeSem o c2 s1 = (none, s')) :
    PancakeSem o (.seq c1 c2) s = (none, s') := by
  have hcl : ({ s1 with clock := min s.clock s1.clock } : PancakeState σ) = s1 := by
    rw [hclk, Nat.min_self, ← hclk]
  rw [PancakeSem]
  simp only [h1, clampClock]
  rw [hcl]; exact h2

@[simp] theorem afterStore_locals (s : PancakeState σ) (a : Word) (bt : BitVec 8) :
    (afterStore s a bt).locals = s.locals := rfl
@[simp] theorem afterStore_memaddrs (s : PancakeState σ) (a : Word) (bt : BitVec 8) :
    (afterStore s a bt).memaddrs = s.memaddrs := rfl
@[simp] theorem afterStore_be (s : PancakeState σ) (a : Word) (bt : BitVec 8) :
    (afterStore s a bt).be = s.be := rfl
@[simp] theorem afterStore_clock (s : PancakeState σ) (a : Word) (bt : BitVec 8) :
    (afterStore s a bt).clock = s.clock := rfl

/-- **THE BYTE-LANDING INDUCTION.** Running the emitted model store list from a state
whose `dst` holds `base` lands each byte at its address (read back via the faithful
`memLoadByte`), and leaves every un-written byte address untouched — the byte-level
frame, which survives sub-word packing (unlike a cell frame). -/
theorem storesRun (o : Oracle σ) (dst : String) (base : Word) :
    ∀ (ps : List (Nat × Nat)) (s : PancakeState σ),
      s.locals dst = some base →
      (∀ p ∈ ps, s.memaddrs (byteAlign (base + BitVec.ofNat 64 p.1)) = true) →
      (∀ p ∈ ps, ∀ q ∈ ps, p.1 ≠ q.1 →
          base + BitVec.ofNat 64 p.1 ≠ base + BitVec.ofNat 64 q.1) →
      (ps.map Prod.fst).Nodup →
      ∃ s', PancakeSem o (storesModel dst ps) s = (none, s')
        ∧ s'.locals = s.locals ∧ s'.memaddrs = s.memaddrs
        ∧ (∀ p ∈ ps, memLoadByte s'.memory s.memaddrs s.be
              (base + BitVec.ofNat 64 p.1) = some ((BitVec.ofNat 64 p.2).setWidth 8))
        ∧ (∀ adr', (∀ p ∈ ps, adr' ≠ base + BitVec.ofNat 64 p.1) →
              memLoadByte s'.memory s.memaddrs s.be adr'
                = memLoadByte s.memory s.memaddrs s.be adr') := by
  intro ps
  induction ps with
  | nil =>
    intro s _ _ _ _
    refine ⟨s, ?_, rfl, rfl, ?_, ?_⟩
    · show PancakeSem o PancakeProg.skip s = (none, s); rw [PancakeSem]
    · intro p hp; simp at hp
    · intro adr' _; rfl
  | cons p ps' ih =>
    intro s hbase haddr hdist hnodup
    -- the head store lands `afterStore`
    have haddrp : s.memaddrs (byteAlign (base + BitVec.ofNat 64 p.1)) = true := haddr p (by simp)
    have hhead : PancakeSem o (.storeByte (addrModel dst p.1) (.const (BitVec.ofNat 64 p.2))) s
        = (none, afterStore s (base + BitVec.ofNat 64 p.1) ((BitVec.ofNat 64 p.2).setWidth 8)) :=
      run_headStore o s dst base p.1 p.2 hbase haddrp
    have hnodupT : (ps'.map Prod.fst).Nodup := (List.nodup_cons.mp (by simpa using hnodup)).2
    have hpnotin : p.1 ∉ ps'.map Prod.fst := (List.nodup_cons.mp (by simpa using hnodup)).1
    -- p.1 differs from every tail offset
    have hne_off : ∀ q ∈ ps', p.1 ≠ q.1 := by
      intro q hq hqe
      exact hpnotin (by rw [hqe]; exact List.mem_map_of_mem hq)
    have hne_adr : ∀ q ∈ ps', (base + BitVec.ofNat 64 p.1) ≠ base + BitVec.ofNat 64 q.1 := by
      intro q hq
      exact hdist p (by simp) q (by simp [hq]) (hne_off q hq)
    cases ps' with
    | nil =>
      -- ps = [p] : storesModel is the bare head store
      refine ⟨afterStore s (base + BitVec.ofNat 64 p.1) ((BitVec.ofNat 64 p.2).setWidth 8),
              ?_, rfl, rfl, ?_, ?_⟩
      · simp only [storesModel]; exact hhead
      · intro q hq
        simp only [List.mem_singleton] at hq; subst q
        exact load_afterStore_same s (base + BitVec.ofNat 64 p.1) _ haddrp
      · intro adr' hfr
        exact load_afterStore_ne s (base + BitVec.ofNat 64 p.1) adr' _ (hfr p (by simp))
    | cons q rest =>
      -- ps = p :: q :: rest : storesModel is a seq (head ; tail)
      obtain ⟨s', hsem, hloc, hma, hland, hframe⟩ :=
        ih (afterStore s (base + BitVec.ofNat 64 p.1) ((BitVec.ofNat 64 p.2).setWidth 8))
           hbase
           (by intro r hr; exact haddr r (by simp [hr]))
           (by intro a ha b hb hab; exact hdist a (by simp [ha]) b (by simp [hb]) hab)
           hnodupT
      refine ⟨s', ?_, hloc, hma, ?_, ?_⟩
      · -- compose seq
        have hunf : storesModel dst (p :: q :: rest)
            = .seq (.storeByte (addrModel dst p.1) (.const (BitVec.ofNat 64 p.2)))
                   (storesModel dst (q :: rest)) := rfl
        rw [hunf]
        exact sem_seq_none' o hhead rfl hsem
      · intro p' hp'
        rcases List.mem_cons.mp hp' with hpe | hin
        · -- head byte survives the tail (byte-frame at its address, then read-back)
          subst p'
          have h1 := hframe (base + BitVec.ofNat 64 p.1) hne_adr
          simp only [afterStore_memaddrs, afterStore_be] at h1
          rw [h1]
          exact load_afterStore_same s (base + BitVec.ofNat 64 p.1) _ haddrp
        · have h2 := hland p' hin
          simp only [afterStore_memaddrs, afterStore_be] at h2
          exact h2
      · intro adr' hfrall
        have h1 := hframe adr' (by intro r hr; exact hfrall r (by simp [hr]))
        simp only [afterStore_memaddrs, afterStore_be] at h1
        rw [h1]
        exact load_afterStore_ne s (base + BitVec.ofNat 64 p.1) adr' _ (hfrall p (by simp))





/-- **Byte-addressed** region contents: reading byte `i` at consecutive byte address
`base + i` via the faithful `mem_load_byte` returns byte `bs[i]` (its low-8 image).
The byte-store analogue of the word-addressed `MemBytesAt`. -/
def MemBytesAtB (m : Word → Word) (dm : Word → Bool) (be : Bool)
    (base : Word) (bs : List Nat) : Prop :=
  ∀ i, i < bs.length →
    memLoadByte m dm be (base + BitVec.ofNat 64 i)
      = some ((BitVec.ofNat 64 bs[i]!).setWidth 8)

/-- **THE BYTE-STORE LANDING LEMMA.** Running the model `storeByte` program that the
emitted response head lowers to lands the byte string `bs` byte-addressed at `base`:
every byte reads back at its own address, even where consecutive bytes pack into one
64-bit word (the sub-word case `MemBytesAt`/`storeLit` cannot express). -/
theorem storesModel_landsB (o : Oracle σ) (dst : String) (base : Word) (bs : List Nat)
    (s : PancakeState σ)
    (hbase : s.locals dst = some base)
    (haddr : ∀ i, i < bs.length →
        s.memaddrs (byteAlign (base + BitVec.ofNat 64 i)) = true)
    (hinj : ∀ i j, i < bs.length → j < bs.length → i ≠ j →
        base + BitVec.ofNat 64 i ≠ base + BitVec.ofNat 64 j) :
    ∃ s', PancakeSem o (storesModel dst ((List.range bs.length).zip bs)) s = (none, s')
      ∧ s'.memaddrs = s.memaddrs
      ∧ MemBytesAtB s'.memory s.memaddrs s.be base bs := by
  obtain ⟨s', hsem, _, hma, hland, _⟩ :=
    storesRun o dst base ((List.range bs.length).zip bs) s hbase
      (by intro p hp
          obtain ⟨a, b⟩ := p
          exact haddr a (by simpa using (List.of_mem_zip hp).1))
      (by intro p hp q hq hpq
          obtain ⟨a, b⟩ := p; obtain ⟨c, d⟩ := q
          exact hinj a c (by simpa using (List.of_mem_zip hp).1)
                        (by simpa using (List.of_mem_zip hq).1) hpq)
      (by rw [List.map_fst_zip (by simp)]; exact List.nodup_range)
  refine ⟨s', hsem, hma, ?_⟩
  intro i hi
  have hmem : (i, bs[i]!) ∈ (List.range bs.length).zip bs := by
    have hlen : i < ((List.range bs.length).zip bs).length := by simp [List.length_zip, hi]
    have hz : ((List.range bs.length).zip bs)[i] = (i, bs[i]!) := by
      rw [List.getElem_zip]; simp [List.getElem_range, hi, getElem!_pos]
    rw [← hz]; exact List.getElem_mem hlen
  have hh := hland (i, bs[i]!) hmem
  simpa using hh

/-- **END-TO-END HEAD CORRECTNESS.** The EMITTED per-byte `st8` head `storesInto dst bs`
lowers (parse-faithful `lower`, the SYNTACTIC half from `LowerBridge`) to a named model
program `P`, and running `P` LANDS the bytes `bs` byte-addressed (the SEMANTIC half). So
the printed `.pnk` response head is correct from emitted-syntax to landed-bytes. -/
theorem serve_head_landsB (o : Oracle σ) (dst : String) (base : Word) (bs : List Nat)
    (s : PancakeState σ)
    (hbase : s.locals dst = some base)
    (haddr : ∀ i, i < bs.length →
        s.memaddrs (byteAlign (base + BitVec.ofNat 64 i)) = true)
    (hinj : ∀ i j, i < bs.length → j < bs.length → i ≠ j →
        base + BitVec.ofNat 64 i ≠ base + BitVec.ofNat 64 j) :
    ∃ P, lowerStmtsFold (storesInto dst bs) = some P
      ∧ ∃ s', PancakeSem o P s = (none, s')
          ∧ MemBytesAtB s'.memory s.memaddrs s.be base bs := by
  refine ⟨storesModel dst ((List.range bs.length).zip bs),
          Pancake.LowerBridge.storesInto_lowers dst bs, ?_⟩
  obtain ⟨s', hsem, _, hmb⟩ := storesModel_landsB o dst base bs s hbase haddr hinj
  exact ⟨s', hsem, hmb⟩

#print axioms getByteAt_setByteAt_same
#print axioms getByteAt_setByteAt_ne
#print axioms byteAlign_byteIndex_inj
#print axioms storesRun
#print axioms storesModel_landsB
#print axioms serve_head_landsB

end Pancake.LowerBridgeSem
