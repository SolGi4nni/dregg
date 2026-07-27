/-
  Pancake/ModelUnify.lean — AXIS 1: UNIFY the byte-addressed and word-slot memory
  models so the full-response compile can proceed (the emission-splice residual).
  DreggNet-only; owns a NEW disjoint file (edits nothing else).

  THE TWO MODELS (as StatusLineEmit §4 names them).
   * WORD-SLOT (legacy shortcut): `storeLit`/`respEmit` (StructEmit) and the
     `copyWhile` write loop (SerializeCompile) write ONE byte per 64-bit SLOT
     (`s.memory (base+i) = wordOfByte bs[i]`), read back by `Load One`. Simple,
     but 8× wasteful and NOT what the wire/cake needs.
   * BYTE-ADDRESSED (faithful): `natToDecProg` (NatToDecFull) renders the status
     decimal at runtime via `StoreByte`/`putByte` into a real PACKED byte buffer,
     read back by the faithful `mem_load_byte` (`memLoadByte`) — 8 bytes per word,
     addressed by byte address. This is what a real packed byte buffer is.

  THE CHOSEN PATH: (b) BYTE-REMODEL. The faithful byte-addressed layout is the
  RIGHT target (a real packed byte buffer is what cake / the wire needs), so we
  do the WHOLE head in the byte-addressed `memLoadByte`/`putByte` model and drop
  the word-slot shortcut. NO bridge lemma between the two images is needed on the
  faithful path: `natToDecProg` ALREADY writes byte-addressed, and here we supply
  the byte-addressed LITERAL materializer (`byteLit`, the `StoreByte`-model
  analogue of the word-slot `storeLit`) with a COMPLETE post-condition, so the two
  compose directly in ONE model. (This is exactly LowerBridgeSem's `MemBytesAtB`
  world; `byteLit`'s landing is the `storeLit`-shaped literal write reproved with
  `putByte` — the sub-word-packing-faithful primitive `NatToDecFull` supplies.)

  WHAT THIS PROVES.
   * `byteLit` / `byteLitFrom_correct` / `byteLit_landsB` — the literal byte
     materializer in the byte-addressed model: straight-line `StoreByte`s land the
     byte string at consecutive BYTE addresses (read back by `memLoadByte`),
     preserving every un-written byte AND every state field (memaddrs/be/locals/
     clock). The `storeLit` analogue, faithful to sub-word packing.
   * `statusHeadProg` / `statusHead_landsB` — THE COMPOSITION: a literal prefix
     byte-write, then `natToDecProg` (runtime decimal render), then a literal
     suffix byte-write, all in the ONE byte-addressed model, assemble the whole
     STATUS-LINE HEAD `pfx ++ natToDec status ++ sfx` byte-addressed at `obase`.
     The status VALUE is runtime (local "status"); the field WIDTH `W` is static
     (3 for HTTP) — exactly the StatusLineEmit §4 story, now COMPOSED, not named.
   * `statusHead_fires_on_404` — a concrete `HTTP/1.1 404 Not Found\r\n` head
     assembles byte-addressed at address 0, every hypothesis discharged (a FACT,
     not an implication); `witness_pre_not_head` pins non-vacuity (the pre-state
     does not already hold the bytes); `head404_is_serialize_prefix` ties the
     assembled bytes to the REAL `serialize` spec (they are its literal prefix).

  (⊆ {propext, Classical.choice, Quot.sound}). Stack L (Lean model of Pancake).
-/
import Pancake.StatusLineEmit

namespace Pancake.ModelUnify

open Pancake Pancake.EmitCorrect Pancake.BytesModel Pancake.SerializeCompile
open Pancake.NatToDecFull Pancake.StatusLineEmit

variable {σ : Type}

/-! ## 0. Word-offset algebra (no wrap side conditions
needed beyond `< 2^64`). -/

/-- `ofNat` is additive at the BitVec level. -/
theorem ofNat_add (a b : Nat) :
    BitVec.ofNat 64 (a + b) = BitVec.ofNat 64 a + BitVec.ofNat 64 b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- Offset join: `(base + a) + b = base + (a + b)`. -/
theorem addr_join (base : Word) (a b : Nat) :
    (base + BitVec.ofNat 64 a) + BitVec.ofNat 64 b = base + BitVec.ofNat 64 (a + b) := by
  rw [ofNat_add, BitVec.add_assoc]

/-- Descending window ↔ absolute offset: `base + a - b = base + (a - b)` for `b ≤ a`. -/
theorem addr_sub (base : Word) (a b : Nat) (hba : b ≤ a) :
    base + BitVec.ofNat 64 a - BitVec.ofNat 64 b = base + BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- Truncating a byte widened to a word recovers the byte (`w2w` round-trip). -/
theorem setWidth64_8 (b : BitVec 8) : (b.setWidth 64).setWidth 8 = b := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro k hk
  simp [hk]

/-! ## 1. `getElem!` over the head's three-way append (spec side, plumbing). -/

theorem get!_some {α} [Inhabited α] (l : List α) (i : Nat) (h : i < l.length) :
    l[i]? = some l[i]! := by
  rw [List.getElem?_eq_getElem h, getElem!_pos l i h]

theorem get!_append_left {α} [Inhabited α] (l1 l2 : List α) (i : Nat) (h : i < l1.length) :
    (l1 ++ l2)[i]! = l1[i]! := by
  rw [getElem!_pos (l1 ++ l2) i (by rw [List.length_append]; omega),
      getElem!_pos l1 i h, List.getElem_append_left h]

theorem get!_append_right {α} [Inhabited α] (l1 l2 : List α) (i : Nat)
    (h1 : l1.length ≤ i) (h2 : i < l1.length + l2.length) :
    (l1 ++ l2)[i]! = l2[i - l1.length]! := by
  have hi : i < (l1 ++ l2).length := by rw [List.length_append]; omega
  have hj : i - l1.length < l2.length := by omega
  rw [getElem!_pos (l1 ++ l2) i hi, getElem!_pos l2 (i - l1.length) hj,
      List.getElem_append_right h1]

/-! ## 2. THE BYTE-ADDRESSED LITERAL MATERIALIZER (`storeLit`, faithful remodel)

`byteLit base bs` writes `bs` at consecutive BYTE addresses `base + i` with the
model's `StoreByte` (`mem_store_byte` = `byteAlign`+`setByte`, the packed-byte
primitive), read back by the faithful `mem_load_byte`. This is the `storeLit`
analogue in the byte-addressed model — the piece the word-slot `storeLit` was the
legacy shortcut for. -/

/-- One literal byte store: `StoreByte (const a) (const (b widened))`. -/
def byteStore (a : Word) (b : BitVec 8) : PancakeProg :=
  .storeByte (.const a) (.const (b.setWidth 64))

/-- Straight-line literal materialization of `bs` at `base + off`, wire order. -/
def byteLitFrom (base : Word) (off : Nat) : Bytes → PancakeProg
  | []      => .skip
  | b :: bs => .seq (byteStore (base + BitVec.ofNat 64 off) b) (byteLitFrom base (off + 1) bs)

/-- The literal materializer: lay `bs` at `base`. -/
def byteLit (base : Word) (bs : Bytes) : PancakeProg := byteLitFrom base 0 bs

/-- One byte store lands `putByte` (the `mem_store_byte` image). -/
theorem byteStore_run (o : Oracle σ) (s : PancakeState σ) (a : Word) (b : BitVec 8)
    (hdm : s.memaddrs (byteAlign a) = true) :
    PancakeSem o (byteStore a b) s
      = (none, { s with memory := putByte s.memory s.be a b }) := by
  have hd : eval s (.const a) = some a := rfl
  have hs : eval s (.const (b.setWidth 64)) = some (b.setWidth 64) := rfl
  have hm : memStoreByte s.memory s.memaddrs s.be a ((b.setWidth 64).setWidth 8)
      = some (putByte s.memory s.be a b) := by
    rw [setWidth64_8]; exact memStore_eq s.memory s.memaddrs s.be a b hdm
  rw [byteStore, evaluate_storeByte o s hd hs hm]

/-- **THE MATERIALIZATION IS CORRECT.** For ALL `bs` and offsets: the straight-line
`StoreByte`s land every byte at its BYTE address (read back by `memLoadByte`),
preserve every un-written byte address (byte-level frame — survives sub-word
packing, unlike a cell frame), and preserve `memaddrs`, `be`, locals and clock.
Nothing about the CONTENT of memory is assumed; the bytes come from the program.
Injectivity on `[0, N)` is the standard "output region does not alias itself". -/
theorem byteLitFrom_correct (o : Oracle σ) (base : Word) (N : Nat)
    (hinj : ∀ p q, p < N → q < N → p ≠ q →
      base + BitVec.ofNat 64 p ≠ base + BitVec.ofNat 64 q) :
    ∀ (bs : Bytes) (off : Nat) (s : PancakeState σ), off + bs.length ≤ N →
      (∀ j, j < bs.length →
        s.memaddrs (byteAlign (base + BitVec.ofNat 64 (off + j))) = true) →
      ∃ s', PancakeSem o (byteLitFrom base off bs) s = (none, s')
        ∧ (∀ j, j < bs.length →
            memLoadByte s'.memory s.memaddrs s.be (base + BitVec.ofNat 64 (off + j))
              = some bs[j]!)
        ∧ (∀ a, (∀ j, j < bs.length → a ≠ base + BitVec.ofNat 64 (off + j)) →
            memLoadByte s'.memory s.memaddrs s.be a = memLoadByte s.memory s.memaddrs s.be a)
        ∧ s'.memaddrs = s.memaddrs ∧ s'.be = s.be ∧ s'.locals = s.locals ∧ s'.clock = s.clock := by
  intro bs
  induction bs with
  | nil =>
    intro off s _ _
    refine ⟨s, ?_, ?_, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
    · show PancakeSem o PancakeProg.skip s = (none, s); rw [PancakeSem]
    · intro j hj; simp at hj
  | cons b bs ih =>
    intro off s hle haddr
    have hlen : off + bs.length + 1 ≤ N := by simp only [List.length_cons] at hle; omega
    have hoff : off < N := by omega
    have haddr0 : s.memaddrs (byteAlign (base + BitVec.ofNat 64 off)) = true := by
      have := haddr 0 (by simp); simpa using this
    let s1 : PancakeState σ := { s with memory := putByte s.memory s.be (base + BitVec.ofNat 64 off) b }
    have h1 : PancakeSem o (byteStore (base + BitVec.ofNat 64 off) b) s = (none, s1) :=
      byteStore_run o s (base + BitVec.ofNat 64 off) b haddr0
    -- tail addressability from `s1`
    have haddr' : ∀ j, j < bs.length →
        s1.memaddrs (byteAlign (base + BitVec.ofNat 64 (off + 1 + j))) = true := by
      intro j hj
      show s.memaddrs _ = true
      have := haddr (j + 1) (by simp only [List.length_cons]; omega)
      rwa [show off + (j + 1) = off + 1 + j from by omega] at this
    obtain ⟨s', hrun, hval, hframe, hma, hbe, hloc, hclk⟩ := ih (off + 1) s1 (by omega) haddr'
    refine ⟨s', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show PancakeSem o (.seq (byteStore (base + BitVec.ofNat 64 off) b)
            (byteLitFrom base (off + 1) bs)) s = (none, s')
      rw [seq_step o h1 (Nat.le_of_eq (rfl : s1.clock = s.clock))]; exact hrun
    · -- landing
      intro j hj
      cases j with
      | zero =>
        have hcond : ∀ k, k < bs.length →
            base + BitVec.ofNat 64 off ≠ base + BitVec.ofNat 64 (off + 1 + k) := by
          intro k hk; exact hinj off (off + 1 + k) hoff (by omega) (by omega)
        have hstep1 : memLoadByte s'.memory s.memaddrs s.be (base + BitVec.ofNat 64 off)
            = memLoadByte s1.memory s.memaddrs s.be (base + BitVec.ofNat 64 off) :=
          hframe (base + BitVec.ofNat 64 off) hcond
        have hstep2 : memLoadByte s1.memory s.memaddrs s.be (base + BitVec.ofNat 64 off)
            = some b :=
          load_putByte_same s.memory s.memaddrs s.be (base + BitVec.ofNat 64 off) b haddr0
        show memLoadByte s'.memory s.memaddrs s.be (base + BitVec.ofNat 64 (off + 0)) = _
        rw [show off + 0 = off from rfl, hstep1, hstep2]
        rw [show (b :: bs)[0]! = b from rfl]
      | succ j' =>
        have hj' : j' < bs.length := by simp only [List.length_cons] at hj; omega
        have hv := hval j' hj'
        show memLoadByte s'.memory s.memaddrs s.be (base + BitVec.ofNat 64 (off + (j' + 1))) = _
        rw [show off + (j' + 1) = off + 1 + j' from by omega,
            show (b :: bs)[j' + 1]! = bs[j']! from rfl]
        exact hv
    · -- frame
      intro a ha
      have haTail : ∀ j, j < bs.length → a ≠ base + BitVec.ofNat 64 (off + 1 + j) := by
        intro j hj
        have := ha (j + 1) (by simp only [List.length_cons]; omega)
        rwa [show off + (j + 1) = off + 1 + j from by omega] at this
      have hHead : a ≠ base + BitVec.ofNat 64 off := by
        have := ha 0 (by simp); simpa using this
      have hs1 : memLoadByte s'.memory s.memaddrs s.be a
          = memLoadByte s1.memory s.memaddrs s.be a := hframe a haTail
      rw [hs1]
      exact load_putByte_diff s.memory s.memaddrs s.be (base + BitVec.ofNat 64 off) b a hHead
    · exact hma
    · exact hbe
    · exact hloc
    · exact hclk

/-! ## 3. The byte-region predicate and `byteLit`'s landing. -/

/-- Byte-addressed region contents (a `BitVec 8` view of `LowerBridgeSem.MemBytesAtB`):
byte `i` reads back at `base + i` via the faithful `mem_load_byte`. -/
def MemBytesB (m : Word → Word) (dm : Word → Bool) (be : Bool) (base : Word) (bs : Bytes) : Prop :=
  ∀ i, i < bs.length → memLoadByte m dm be (base + BitVec.ofNat 64 i) = some bs[i]!

/-- **`byteLit` lands the byte string byte-addressed.** -/
theorem byteLit_landsB (o : Oracle σ) (base : Word) (bs : Bytes) (s : PancakeState σ)
    (hinj : ∀ p q, p < bs.length → q < bs.length → p ≠ q →
      base + BitVec.ofNat 64 p ≠ base + BitVec.ofNat 64 q)
    (haddr : ∀ j, j < bs.length → s.memaddrs (byteAlign (base + BitVec.ofNat 64 j)) = true) :
    ∃ s', PancakeSem o (byteLit base bs) s = (none, s')
      ∧ MemBytesB s'.memory s.memaddrs s.be base bs
      ∧ (∀ a, (∀ j, j < bs.length → a ≠ base + BitVec.ofNat 64 j) →
          memLoadByte s'.memory s.memaddrs s.be a = memLoadByte s.memory s.memaddrs s.be a)
      ∧ s'.memaddrs = s.memaddrs ∧ s'.be = s.be ∧ s'.locals = s.locals ∧ s'.clock = s.clock := by
  obtain ⟨s', hrun, hval, hframe, hma, hbe, hloc, hclk⟩ :=
    byteLitFrom_correct o base bs.length hinj bs 0 s (by omega)
      (by intro j hj; simpa using haddr j hj)
  refine ⟨s', hrun, ?_, ?_, hma, hbe, hloc, hclk⟩
  · intro i hi; have := hval i hi; simpa using this
  · intro a ha; exact hframe a (by intro j hj; simpa using ha j hj)

/-! ## 4. THE COMPOSITION — the status-line HEAD in ONE byte-addressed model

`statusHeadProg`: a literal prefix byte-write, then `natToDecProg` (runtime
decimal render), then a literal suffix byte-write. The status VALUE is a runtime
local ("status"); the field WIDTH `W` is a static program constant (3 for HTTP).
Splicing `natToDecProg` INTO the literal frame — the exact emission-splice the
model-unification residual was blocking — now happens in ONE model. -/

/-- THE HEAD PROGRAM. `byteLit pfx ; n := status ; p := obase+|pfx|+W ;
natToDecProg ; byteLit sfx`. -/
def statusHeadProg (obase : Word) (pfx : Bytes) (W : Nat) (sfx : Bytes) : PancakeProg :=
  .seq (byteLit obase pfx)
  (.seq (.assign "n" (.var "status"))
  (.seq (.assign "p" (.const (obase + BitVec.ofNat 64 (pfx.length + W))))
  (.seq natToDecProg
        (byteLit (obase + BitVec.ofNat 64 (pfx.length + W)) sfx))))

/-- **THE HEAD ASSEMBLES BYTE-ADDRESSED IN ONE MODEL.** For a runtime status
(local "status"), a STATIC field width `W = (natToDec status).length`, and a
prefix/suffix of literal bytes: running `statusHeadProg` lays the whole head
`pfx ++ natToDec status ++ sfx` at consecutive BYTE addresses `obase + i`, read
back by the faithful `mem_load_byte`. The literal frame (`byteLit`, `putByte`
model) and the runtime decimal render (`natToDecProg`, `putByte` model) COMPOSE —
same memory image, no word-slot/byte-addressed bridge required. -/
theorem statusHead_landsB (o : Oracle σ) (obase : Word) (pfx sfx : Bytes)
    (status W : Nat) (s : PancakeState σ)
    (hW : (natToDec status).length = W)
    (hstat63 : status < 2 ^ 63)
    (hstatusL : s.locals "status" = some (BitVec.ofNat 64 status))
    (hinj : ∀ p q, p < pfx.length + W + sfx.length → q < pfx.length + W + sfx.length →
      p ≠ q → obase + BitVec.ofNat 64 p ≠ obase + BitVec.ofNat 64 q)
    (haddr : ∀ i, i < pfx.length + W + sfx.length →
      s.memaddrs (byteAlign (obase + BitVec.ofNat 64 i)) = true)
    (hclk : natFuel status ≤ s.clock) :
    ∃ s', PancakeSem o (statusHeadProg obase pfx W sfx) s = (none, s')
      ∧ MemBytesB s'.memory s.memaddrs s.be obase (pfx ++ natToDec status ++ sfx) := by
  -- ===== Phase A: literal prefix =====
  obtain ⟨s1, hrunA, hmbA, _hframeA, hmaA, hbeA, hlocA, hclkA⟩ :=
    byteLit_landsB o obase pfx s
      (fun p q hp hq hpq => hinj p q (by omega) (by omega) hpq)
      (fun j hj => haddr j (by omega))
  -- ===== assigns: n := status, p := obase + |pfx| + W =====
  let s2 : PancakeState σ := { s1 with locals := setLocal s1.locals "n" (BitVec.ofNat 64 status) }
  let s3 : PancakeState σ := { s1 with locals := (setLocal (setLocal s1.locals "n" (BitVec.ofNat 64 status)) "p" (obase + BitVec.ofNat 64 (pfx.length + W))) }
  have hevalStatus : eval s1 (.var "status") = some (BitVec.ofNat 64 status) := by
    show s1.locals "status" = _; rw [hlocA]; exact hstatusL
  have hA2 : PancakeSem o (.assign "n" (.var "status")) s1 = (none, s2) :=
    sem_assign (oracle := o) (x := "n") hevalStatus
  have hevalP : eval s2 (.const (obase + BitVec.ofNat 64 (pfx.length + W)))
      = some (obase + BitVec.ofNat 64 (pfx.length + W)) := rfl
  have hA3 : PancakeSem o (.assign "p" (.const (obase + BitVec.ofNat 64 (pfx.length + W)))) s2
      = (none, s3) := sem_assign (oracle := o) (x := "p") hevalP
  -- s3 field facts
  have hma3 : s3.memaddrs = s.memaddrs := hmaA
  have hbe3 : s3.be = s.be := hbeA
  have hclk3 : s3.clock = s.clock := hclkA
  have hn3 : s3.locals "n" = some (BitVec.ofNat 64 status) := by
    show setLocal (setLocal s1.locals "n" (BitVec.ofNat 64 status)) "p"
      (obase + BitVec.ofNat 64 (pfx.length + W)) "n" = some (BitVec.ofNat 64 status)
    rw [setLocal_ne _ _ _ (by decide), setLocal_same]
  have hp3 : s3.locals "p" = some (obase + BitVec.ofNat 64 (pfx.length + W)) := by
    show setLocal (setLocal s1.locals "n" (BitVec.ofNat 64 status)) "p"
      (obase + BitVec.ofNat 64 (pfx.length + W)) "p" = some (obase + BitVec.ofNat 64 (pfx.length + W))
    rw [setLocal_same]
  -- ===== Phase B: natToDecProg (runtime decimal render) =====
  have hdm3 : ∀ j, j < (natToDec status).length →
      s3.memaddrs (byteAlign ((obase + BitVec.ofNat 64 (pfx.length + W))
        - BitVec.ofNat 64 (j + 1))) = true := by
    intro j hj
    have hjW : j < W := by rw [← hW]; exact hj
    rw [addr_sub obase (pfx.length + W) (j + 1) (by omega), hma3]
    exact haddr (pfx.length + W - (j + 1)) (by omega)
  obtain ⟨s4, hrunB, hclkB, hpostB⟩ :=
    natToDecProg_sem o status (obase + BitVec.ofNat 64 (pfx.length + W)) s3
      hstat63 hn3 hp3 hdm3 (by rw [hclk3]; exact hclk)
  obtain ⟨_hn4, _hp4, hbytes4, hfr4, hma4, hbe4, _hba4, _hlfr4⟩ := hpostB
  have hma4s : s4.memaddrs = s.memaddrs := by rw [hma4]; exact hma3
  have hbe4s : s4.be = s.be := by rw [hbe4]; exact hbe3
  -- ===== Phase C: literal suffix =====
  have hinjC : ∀ p q, p < sfx.length → q < sfx.length → p ≠ q →
      (obase + BitVec.ofNat 64 (pfx.length + W)) + BitVec.ofNat 64 p
        ≠ (obase + BitVec.ofNat 64 (pfx.length + W)) + BitVec.ofNat 64 q := by
    intro p q hp hq hpq
    rw [addr_join, addr_join]
    exact hinj (pfx.length + W + p) (pfx.length + W + q) (by omega) (by omega) (by omega)
  have haddrC : ∀ j, j < sfx.length →
      s4.memaddrs (byteAlign ((obase + BitVec.ofNat 64 (pfx.length + W))
        + BitVec.ofNat 64 j)) = true := by
    intro j hj
    rw [addr_join, hma4s]
    exact haddr (pfx.length + W + j) (by omega)
  obtain ⟨s5, hrunC, hmbC, hframeC, hmaC, hbeC, _hlocC, _hclkC⟩ :=
    byteLit_landsB o (obase + BitVec.ofNat 64 (pfx.length + W)) sfx s4 hinjC haddrC
  -- ===== the run: chain the four seqs =====
  refine ⟨s5, ?_, ?_⟩
  · show PancakeSem o (statusHeadProg obase pfx W sfx) s = (none, s5)
    rw [statusHeadProg]
    rw [seq_step o hrunA (Nat.le_of_eq hclkA)]
    rw [seq_step o hA2 (Nat.le_of_eq rfl)]
    rw [seq_step o hA3 (Nat.le_of_eq rfl)]
    rw [seq_step o hrunB (by rw [hclkB]; omega)]
    exact hrunC
  -- ===== the assembled bytes =====
  · intro i hi
    have hlenTot : (pfx ++ natToDec status ++ sfx).length = pfx.length + W + sfx.length := by
      rw [List.length_append, List.length_append, hW]
    rw [hlenTot] at hi
    by_cases hpfx : i < pfx.length
    · -- prefix byte
      have hne_sfx : ∀ k, k < sfx.length → obase + BitVec.ofNat 64 i
          ≠ (obase + BitVec.ofNat 64 (pfx.length + W)) + BitVec.ofNat 64 k := by
        intro k hk; rw [addr_join]
        exact hinj i (pfx.length + W + k) (by omega) (by omega) (by omega)
      have e1 := hframeC (obase + BitVec.ofNat 64 i) hne_sfx
      have hne_dig : ∀ j, j < (natToDec status).length → obase + BitVec.ofNat 64 i
          ≠ (obase + BitVec.ofNat 64 (pfx.length + W)) - BitVec.ofNat 64 (j + 1) := by
        intro j hj
        have hjW : j < W := by rw [← hW]; exact hj
        rw [addr_sub obase (pfx.length + W) (j + 1) (by omega)]
        exact hinj i (pfx.length + W - (j + 1)) (by omega) (by omega) (by omega)
      have e2 := hfr4 (obase + BitVec.ofNat 64 i) hne_dig
      have e3 : memLoadByte s3.memory s.memaddrs s.be (obase + BitVec.ofNat 64 i)
          = some pfx[i]! := hmbA i hpfx
      rw [hma4s, hbe4s] at e1
      rw [hma4s, hbe4s, hma3, hbe3] at e2
      show memLoadByte s5.memory s.memaddrs s.be (obase + BitVec.ofNat 64 i)
        = some (pfx ++ natToDec status ++ sfx)[i]!
      rw [get!_append_left (pfx ++ natToDec status) sfx i (by rw [List.length_append]; omega),
          get!_append_left pfx (natToDec status) i hpfx]
      rw [e1, e2, e3]
    · by_cases hdig : i < pfx.length + W
      · -- digit byte
        have hji : pfx.length ≤ i := Nat.not_lt.mp hpfx
        have hjL : i - pfx.length < (natToDec status).length := by rw [hW]; omega
        have hdaddr : (obase + BitVec.ofNat 64 (pfx.length + W))
            - BitVec.ofNat 64 ((natToDec status).length - (i - pfx.length))
            = obase + BitVec.ofNat 64 i := by
          rw [addr_sub obase (pfx.length + W) ((natToDec status).length - (i - pfx.length))
                (by rw [hW]; omega),
              show pfx.length + W - ((natToDec status).length - (i - pfx.length)) = i
                from by rw [hW]; omega]
        have hbyte := hbytes4 (i - pfx.length) ((natToDec status)[i - pfx.length]!)
          (get!_some (natToDec status) (i - pfx.length) hjL)
        rw [hdaddr] at hbyte
        have hne_sfx : ∀ k, k < sfx.length → obase + BitVec.ofNat 64 i
            ≠ (obase + BitVec.ofNat 64 (pfx.length + W)) + BitVec.ofNat 64 k := by
          intro k hk; rw [addr_join]
          exact hinj i (pfx.length + W + k) (by omega) (by omega) (by omega)
        have e1 := hframeC (obase + BitVec.ofNat 64 i) hne_sfx
        rw [hma4s, hbe4s] at e1 hbyte
        show memLoadByte s5.memory s.memaddrs s.be (obase + BitVec.ofNat 64 i)
          = some (pfx ++ natToDec status ++ sfx)[i]!
        rw [get!_append_left (pfx ++ natToDec status) sfx i
              (by rw [List.length_append, hW]; omega),
            get!_append_right pfx (natToDec status) i hji (by rw [hW]; omega)]
        rw [e1, hbyte]
      · -- suffix byte
        have hPWi : pfx.length + W ≤ i := by omega
        have hkS : i - (pfx.length + W) < sfx.length := by omega
        have hcaddr : (obase + BitVec.ofNat 64 (pfx.length + W))
            + BitVec.ofNat 64 (i - (pfx.length + W)) = obase + BitVec.ofNat 64 i := by
          rw [addr_join, show pfx.length + W + (i - (pfx.length + W)) = i from by omega]
        have hc := hmbC (i - (pfx.length + W)) hkS
        rw [hcaddr, hma4s, hbe4s] at hc
        show memLoadByte s5.memory s.memaddrs s.be (obase + BitVec.ofNat 64 i)
          = some (pfx ++ natToDec status ++ sfx)[i]!
        rw [get!_append_right (pfx ++ natToDec status) sfx i
              (by rw [List.length_append, hW]; omega)
              (by rw [List.length_append, hW]; omega),
            show i - (pfx ++ natToDec status).length = i - (pfx.length + W)
              from by rw [List.length_append, hW]]
        exact hc

/-! ## 5. NON-VACUITY — a concrete `HTTP/1.1 404 Not Found` head in ONE model

`resp404` (StatusLineEmit) with status 404. Its status-LINE head is
`statusPrefix ++ natToDec 404 ++ sfx404` = `"HTTP/1.1 404 Not Found\r\n"`, a genuine
PREFIX of the REAL `serialize resp404` spec. The emitted head program, run on a
witness state (status 404 in local "status", every address mapped, 100 ticks),
assembles those 24 bytes BYTE-ADDRESSED at address 0 — every hypothesis
discharged, a FACT (not an implication). -/

/-- The status-line suffix for `resp404`: `SP "Not Found" CRLF`. -/
def sfx404 : Bytes := [32] ++ resp404.reason ++ crlf

/-- The assembled status-line head bytes. -/
def head404 : Bytes := statusPrefix ++ natToDec 404 ++ sfx404

-- the head IS `"HTTP/1.1 404 Not Found\r\n"`, 24 bytes; render budget 46:
#guard head404 = [72, 84, 84, 80, 47, 49, 46, 49, 32,   -- "HTTP/1.1 "
                  52, 48, 52,                             -- "404"
                  32, 78, 111, 116, 32, 70, 111, 117, 110, 100,  -- " Not Found"
                  13, 10]                                 -- CRLF
#guard head404.length = 24
#guard natFuel 404 = 46

/-- **THE HEAD IS A PREFIX OF THE REAL `serialize` SPEC.** `head404` is not a
private render: it is the literal opening of `serialize resp404`. -/
theorem head404_is_serialize_prefix :
    ∃ rest, head404 ++ rest = serialize resp404 := by
  refine ⟨headerBlockOf resp404 ++ crlf ++ crlf ++ resp404.body, ?_⟩
  rw [serialize_status_split resp404]
  show statusPrefix ++ natToDec 404 ++ ([32] ++ resp404.reason ++ crlf)
        ++ (headerBlockOf resp404 ++ crlf ++ crlf ++ resp404.body)
      = statusPrefix ++ (natToDec resp404.status ++ statusTail resp404)
  rw [show resp404.status = 404 from rfl]
  simp only [statusTail, List.append_assoc]

/-- The witness state: `status = 404` in local "status", every address mapped, a
100-tick budget, memory all-zero (so the head bytes are NOT hiding in it). -/
def wstate404 (f : σ) : PancakeState σ :=
  { locals := fun n => if n = "status" then some (BitVec.ofNat 64 404) else none,
    memory := fun _ => (0 : Word), memaddrs := fun _ => true, be := false,
    clock := 100, ffi := f, baseAddr := 0 }

/-- **THE COMPOSITION FIRES ON A REAL 404.** Not an implication — every hypothesis
of `statusHead_landsB` is discharged against `wstate404`. Running the head program
`statusHeadProg 0 statusPrefix 3 sfx404` terminates normally and lands the 24 bytes
of `head404 = "HTTP/1.1 404 Not Found\r\n"` byte-addressed at address 0: a literal
prefix write, the RUNTIME decimal render of `404` (via `natToDecProg`, no baked
digits), and a literal suffix write, all in ONE byte-addressed memory image. -/
theorem statusHead_fires_on_404 (o : Oracle σ) (f : σ) :
    ∃ s', PancakeSem o (statusHeadProg 0 statusPrefix 3 sfx404) (wstate404 f) = (none, s')
      ∧ MemBytesB s'.memory (wstate404 f).memaddrs (wstate404 f).be 0 head404 := by
  have hbound : statusPrefix.length + 3 + sfx404.length = 24 := by decide
  refine statusHead_landsB o 0 statusPrefix sfx404 404 3 (wstate404 f)
    (by decide) (by omega) rfl ?_ (fun i _ => rfl) (by show natFuel 404 ≤ 100; decide)
  -- injectivity of the 24-byte output region at base 0
  intro p q hp hq hpq heq
  rw [hbound] at hp hq
  exact hpq (ofNat64_inj (by omega) (by omega) (by simpa using heq))

/-- **THE PRE-STATE IS NOT THE HEAD.** `wstate404`'s memory is all-zero, so it does
NOT already hold `head404` (byte 0 is `0`, not `'H' = 72`). With
`statusHead_fires_on_404` this pins the result: the program TRANSPORTS a state where
the conclusion is false to one where it is true — the bytes are manufactured by the
composed program, not laundered from the hypotheses. -/
theorem witness_pre_not_head (f : σ) :
    ¬ MemBytesB (wstate404 f).memory (wstate404 f).memaddrs (wstate404 f).be 0 head404 := by
  intro h
  have h0 : memLoadByte (fun _ => (0 : Word)) (fun _ => true) false (0 + BitVec.ofNat 64 0)
      = some head404[0]! := h 0 (by decide)
  exact absurd h0 (by decide)

end Pancake.ModelUnify

-- ASSURANCE: the load-bearing chain uses only the three Lean-core axioms.
#print axioms Pancake.ModelUnify.byteLit_landsB
#print axioms Pancake.ModelUnify.statusHead_landsB
#print axioms Pancake.ModelUnify.statusHead_fires_on_404
#print axioms Pancake.ModelUnify.head404_is_serialize_prefix
#print axioms Pancake.ModelUnify.witness_pre_not_head
