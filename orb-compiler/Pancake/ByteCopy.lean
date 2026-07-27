/-
  Pancake/ByteCopy.lean — AXIS 1: the RUNTIME body-COPY loop, reproved in the
  FAITHFUL byte-addressed StoreByte/putByte memory model.

  THE RESIDUAL THIS CLOSES. `SerializeCompile.copyWhile` / `SerializeFull.writeSeg`
  copy the response body one byte per 64-bit WORD SLOT (`.store` / `.loadWord`,
  read back by `s.memory = wordOfByte …`). That is the legacy word-slot shortcut —
  8× wasteful and NOT a real packed byte buffer. `ModelUnify` moved the response
  HEAD (literal frame + runtime decimal render) into the byte-addressed model
  (`StoreByte`/`putByte`, read back by `memLoadByte`), leaving the body copy as the
  LAST piece still word-slot-only. This file reproves the body copy byte-addressed.

  WHAT THIS PROVES:

   * `copyByteWhile` — the write loop
        while (i < len) { storeByte (dst+i) (loadByte (src+i)); i := i+1 }
     using the model's `StoreByte`/`LoadByte` (packed byte access), NOT the
     word-slot `.store`/`.loadWord`. Each iteration reads ONE byte at the byte
     address `src+i` (`memLoadByte`) and lays it at the byte address `dst+i`
     (`putByte`).

   * `copyByte_step` — ONE iteration advances the byte-addressed invariant. The key
     is that a byte-store at `dst+k` disturbs reads at NO OTHER byte address
     (`load_putByte_diff`), so — exactly as in the word-slot proof but now at BYTE
     granularity, faithful to sub-word packing — the source region and the earlier
     destination prefix survive whenever the write address is distinct (`hdisj` /
     `hinj`). A FRAME clause against the entry memory carries every untouched byte
     through, which is what lets a later program's already-written bytes survive.

   * `copySeg_landsB` — THE STAGE: `copySeg dst src len` sets its own `dst/src/i/len`
     frame, runs `copyByteWhile`, and lands the `len` bytes `val` at consecutive
     BYTE addresses `[dst, dst+len)` (read back by `memLoadByte`), preserving every
     byte outside that window (frame) and `memaddrs`/`be`. Assembled through
     `while_inv_cond_clk` (the clock-accounting loop rule), the same shape as the
     word-slot `refinesClk_copy` and `natToDecProg`.

  This is the runtime body copy in the ONE faithful byte-addressed model — the last
  word-slot residual of the serialize chain, closed. Stack L (Lean model of Pancake).

  (⊆ {propext, Classical.choice, Quot.sound}).
-/
import Pancake.NatToDecFull
import Pancake.EmitCorrectClock
import Pancake.EmitCorrectRegion

namespace Pancake.ByteCopy

open Pancake Pancake.EmitCorrect Pancake.BytesModel Pancake.SerializeCompile
open Pancake.NatToDecFull Pancake.EmitCorrectClock

variable {σ : Type}

/-! ## 0. Byte round-trip (the `storeByte` low-byte truncation is a no-op on a
byte widened to a word). -/

/-- Truncating a byte widened to a word recovers the byte (`w2w` round-trip). The
`StoreByte` semantics store `w.setWidth 8`; when `w = b.setWidth 64` this is `b`. -/
theorem setWidth64_8 (b : BitVec 8) : (b.setWidth 64).setWidth 8 = b := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro k hk
  simp [hk]

/-! ## 1. The byte-addressed copy program. -/

/-- The copy body: `storeByte (dst+i) (loadByte (src+i)); i := i+1`.
`LoadByte`/`StoreByte` are the PACKED byte-access primitives (`memLoadByte`/
`putByte`), 8 bytes per word — not the word-slot `.loadWord`/`.store`. -/
def copyByteBody : PancakeProg :=
  .seq
    (.storeByte (.op .add (.var "dst") (.var "i"))
                (.loadByte (.op .add (.var "src") (.var "i"))))
    (.assign "i" (.op .add (.var "i") (.const (BitVec.ofNat 64 1))))

/-- The write `While`: `while (i < len) copyByteBody`. -/
def copyByteWhile : PancakeProg :=
  .while_ (.cmp .less (.var "i") (.var "len")) copyByteBody

/-- The byte-addressed write invariant, indexed by remaining iterations `n`
(current index `k = len - n`): the loop frame locals; the SOURCE region holds the
intended bytes `val` (read back by `memLoadByte`); the DESTINATION region is byte-
addressable; the first `k` destination bytes already carry `val`; and a FRAME
against the entry memory `m0` — every byte address not yet written reads exactly as
it did at entry (this is what a later program's already-written bytes ride on). -/
def copyInvB (dm : Word → Bool) (be : Bool) (m0 : Word → Word)
    (dst src : Word) (val : Nat → BitVec 8) (len : Nat)
    (n : Nat) (s : PancakeState σ) : Prop :=
  ∃ k, k + n = len ∧
    s.memaddrs = dm ∧ s.be = be ∧
    s.locals "dst" = some dst ∧
    s.locals "src" = some src ∧
    s.locals "i"   = some (BitVec.ofNat 64 k) ∧
    s.locals "len" = some (BitVec.ofNat 64 len) ∧
    (∀ j, j < len → memLoadByte s.memory dm be (src + BitVec.ofNat 64 j) = some (val j)) ∧
    (∀ j, j < len → dm (byteAlign (dst + BitVec.ofNat 64 j)) = true) ∧
    (∀ j, j < k → memLoadByte s.memory dm be (dst + BitVec.ofNat 64 j) = some (val j)) ∧
    (∀ a, (∀ j, j < k → a ≠ dst + BitVec.ofNat 64 j) →
        memLoadByte s.memory dm be a = memLoadByte m0 dm be a)

/-- The copy guard `i < len` evaluates to `0` exactly when the budget is spent. -/
theorem copyByte_guard (dm : Word → Bool) (be : Bool) (m0 : Word → Word)
    (dst src : Word) (val : Nat → BitVec 8) (len : Nat) (hlen63 : len < 2 ^ 63)
    (n : Nat) (s : PancakeState σ)
    (hI : copyInvB dm be m0 dst src val len n s) :
    eval s (.cmp .less (.var "i") (.var "len")) = some (if n = 0 then (0 : Word) else 1) := by
  obtain ⟨k, hkn, _, _, _, _, hi, hlen, _, _, _, _⟩ := hI
  have hk63 : k < 2 ^ 63 := by omega
  have hev : eval s (.cmp .less (.var "i") (.var "len"))
      = some (if signedLt (BitVec.ofNat 64 k) (BitVec.ofNat 64 len) then 1 else 0) := by
    simp only [eval, hi, hlen]
  rw [hev, signedLt_ofNat _ _ hk63 hlen63]
  by_cases hn : n = 0
  · have : k = len := by omega
    subst this; simp [hn]
  · have : k < len := by omega
    simp [hn, this]

/-- **ONE byte-copy iteration advances the invariant.** The `LoadByte` reads
`val k` at `src+k` (`memLoadByte`), the `StoreByte` lays it at the byte address
`dst+k` (`putByte`); source region and the earlier destination prefix survive
because `dst+k` is a distinct BYTE address from every source byte (`hdisj`) and
every earlier destination byte (`hinj`), and `load_putByte_diff` says a byte-store
disturbs reads at no other byte address. -/
theorem copyByte_step (o : Oracle σ) (dm : Word → Bool) (be : Bool) (m0 : Word → Word)
    (dst src : Word) (val : Nat → BitVec 8) (len : Nat)
    (hlen63 : len < 2 ^ 63)
    (hdisj : ∀ i j, i < len → j < len →
      dst + BitVec.ofNat 64 i ≠ src + BitVec.ofNat 64 j)
    (hinj : ∀ i j, i < len → j < len → i ≠ j →
      dst + BitVec.ofNat 64 i ≠ dst + BitVec.ofNat 64 j)
    (n : Nat) (s : PancakeState σ) (hI : copyInvB dm be m0 dst src val len (n + 1) s) :
    ∃ s2, PancakeSem o copyByteBody (decClock s) = (none, s2) ∧
      copyInvB dm be m0 dst src val len n s2 ∧ s2.clock = s.clock - 1 := by
  obtain ⟨k, hkn, hma, hbe, hdst, hsrc, hi, hlen, hsrcR, hdstA, hprog, hfr⟩ := hI
  have hklt : k < len := by omega
  have hdl : (decClock s).locals = s.locals := rfl
  have hdmem : (decClock s).memory = s.memory := rfl
  have hdma : (decClock s).memaddrs = dm := by rw [show (decClock s).memaddrs = s.memaddrs from rfl]; exact hma
  have hdbe : (decClock s).be = be := by rw [show (decClock s).be = s.be from rfl]; exact hbe
  -- store address and the loaded byte
  have haddr : eval (decClock s) (.op .add (.var "dst") (.var "i"))
      = some (dst + BitVec.ofNat 64 k) := by
    simp only [eval, hdl, hdst, hi]
  have hsrcAddr : eval (decClock s) (.op .add (.var "src") (.var "i"))
      = some (src + BitVec.ofNat 64 k) := by
    simp only [eval, hdl, hsrc, hi]
  have hloadB : memLoadByte (decClock s).memory (decClock s).memaddrs (decClock s).be
      (src + BitVec.ofNat 64 k) = some (val k) := by
    rw [hdmem, hdma, hdbe]; exact hsrcR k hklt
  have hload : eval (decClock s) (.loadByte (.op .add (.var "src") (.var "i")))
      = some ((val k).setWidth 64) := by
    show (match eval (decClock s) (.op .add (.var "src") (.var "i")) with
          | some w =>
            (match memLoadByte (decClock s).memory (decClock s).memaddrs (decClock s).be w with
             | some b => some (b.setWidth 64)
             | none => none)
          | none => none) = _
    simp only [hsrcAddr, hloadB]
  -- the byte store into `dst+k`
  have hdmk : dm (byteAlign (dst + BitVec.ofNat 64 k)) = true := hdstA k hklt
  have hstoreEq : memStoreByte (decClock s).memory (decClock s).memaddrs (decClock s).be
      (dst + BitVec.ofNat 64 k) (((val k).setWidth 64).setWidth 8)
      = some (putByte (decClock s).memory (decClock s).be (dst + BitVec.ofNat 64 k) (val k)) := by
    rw [setWidth64_8, hdma, hdbe]
    exact memStore_eq (decClock s).memory dm be (dst + BitVec.ofNat 64 k) (val k) hdmk
  obtain ⟨sS, hsSdef⟩ : ∃ sS : PancakeState σ, sS =
      { (decClock s) with memory := putByte (decClock s).memory (decClock s).be (dst + BitVec.ofNat 64 k) (val k) } := ⟨_, rfl⟩
  have hstore : PancakeSem o (.storeByte (.op .add (.var "dst") (.var "i"))
        (.loadByte (.op .add (.var "src") (.var "i")))) (decClock s) = (none, sS) := by
    rw [hsSdef]; exact evaluate_storeByte o (decClock s) haddr hload hstoreEq
  -- the index bump on sS
  have hsSi : sS.locals "i" = some (BitVec.ofNat 64 k) := by rw [hsSdef]; exact hi
  have hiE : eval sS (.op .add (.var "i") (.const (BitVec.ofNat 64 1)))
      = some (BitVec.ofNat 64 (k + 1)) := by
    show (match eval sS (.var "i"), eval sS (.const (BitVec.ofNat 64 1)) with
          | some x, some y => some (x + y) | _, _ => none) = _
    simp only [eval, hsSi]
    rw [ofNat_add_small _ _ (by omega)]
  obtain ⟨sB, hsBdef⟩ : ∃ sB : PancakeState σ, sB =
      { sS with locals := setLocal sS.locals "i" (BitVec.ofNat 64 (k + 1)) } := ⟨_, rfl⟩
  have hbump : PancakeSem o (.assign "i" (.op .add (.var "i") (.const (BitVec.ofNat 64 1)))) sS
      = (none, sB) := by rw [hsBdef]; exact sem_assign (oracle := o) (x := "i") hiE
  -- body = seq (storeByte) (bump); the clock clamp collapses (store is clock-neutral)
  have hclkSS : sS.clock = (decClock s).clock := by rw [hsSdef]
  have hbody : PancakeSem o copyByteBody (decClock s) = (none, sB) := by
    rw [copyByteBody, sem_seq_none (oracle := o) hstore]
    have hm : min (decClock s).clock sS.clock = sS.clock := by rw [hclkSS]; omega
    rw [hm]
    have : ({ sS with clock := sS.clock } : PancakeState σ) = sS := rfl
    rw [this]; exact hbump
  -- memory / field facts for sB
  have hBmem : sB.memory = putByte s.memory be (dst + BitVec.ofNat 64 k) (val k) := by
    rw [hsBdef]; show sS.memory = _
    rw [hsSdef]; rw [hdmem, hdbe]
  have hBma : sB.memaddrs = dm := by
    rw [hsBdef]; show sS.memaddrs = dm; rw [hsSdef]; exact hdma
  have hBbe : sB.be = be := by
    rw [hsBdef]; show sS.be = be; rw [hsSdef]; exact hdbe
  have hBclk : sB.clock = s.clock - 1 := by
    rw [hsBdef]; show sS.clock = s.clock - 1; rw [hclkSS]; rfl
  -- locals for sB
  have dne1 : ("dst" = "i") = False := by decide
  have dne2 : ("src" = "i") = False := by decide
  have dne3 : ("len" = "i") = False := by decide
  have hBdst : sB.locals "dst" = some dst := by
    rw [hsBdef]; simp only [setLocal, dne1, if_false]; rw [hsSdef]; exact hdst
  have hBsrc : sB.locals "src" = some src := by
    rw [hsBdef]; simp only [setLocal, dne2, if_false]; rw [hsSdef]; exact hsrc
  have hBi : sB.locals "i" = some (BitVec.ofNat 64 (k + 1)) := by
    rw [hsBdef]; simp only [setLocal, if_true]
  have hBlen : sB.locals "len" = some (BitVec.ofNat 64 len) := by
    rw [hsBdef]; simp only [setLocal, dne3, if_false]; rw [hsSdef]; exact hlen
  -- source region survives (write at dst+k is a distinct byte address from src+j)
  have hBsrcR : ∀ j, j < len →
      memLoadByte sB.memory dm be (src + BitVec.ofNat 64 j) = some (val j) := by
    intro j hj
    rw [hBmem]
    rw [load_putByte_diff s.memory dm be (dst + BitVec.ofNat 64 k) (val k)
          (src + BitVec.ofNat 64 j) (fun h => hdisj k j hklt hj h.symm)]
    exact hsrcR j hj
  -- destination prefix now covers k+1
  have hBprog : ∀ j, j < k + 1 →
      memLoadByte sB.memory dm be (dst + BitVec.ofNat 64 j) = some (val j) := by
    intro j hj
    rw [hBmem]
    by_cases hjk : j = k
    · subst hjk
      exact load_putByte_same s.memory dm be (dst + BitVec.ofNat 64 j) (val j) (hdstA j hklt)
    · rw [load_putByte_diff s.memory dm be (dst + BitVec.ofNat 64 k) (val k)
            (dst + BitVec.ofNat 64 j) (hinj j k (by omega) hklt hjk)]
      exact hprog j (by omega)
  -- frame against m0 extends to k+1
  have hBfr : ∀ a, (∀ j, j < k + 1 → a ≠ dst + BitVec.ofNat 64 j) →
      memLoadByte sB.memory dm be a = memLoadByte m0 dm be a := by
    intro a ha
    rw [hBmem]
    rw [load_putByte_diff s.memory dm be (dst + BitVec.ofNat 64 k) (val k) a
          (ha k (by omega))]
    exact hfr a (fun j hj => ha j (by omega))
  refine ⟨sB, hbody, ⟨k + 1, by omega, hBma, hBbe, hBdst, hBsrc, hBi, hBlen,
    hBsrcR, ?_, hBprog, hBfr⟩, hBclk⟩
  intro j hj; exact hdstA j hj

/-! ## 2. `copySeg` — set the frame, run the loop, land the bytes. -/

/-- Set the `dst/src/i/len` frame from constants, then run `copyByteWhile`. -/
def copySeg (dst src : Word) (len : Nat) : PancakeProg :=
  .seq (.assign "dst" (.const dst))
  (.seq (.assign "src" (.const src))
  (.seq (.assign "i"   (.const (BitVec.ofNat 64 0)))
  (.seq (.assign "len" (.const (BitVec.ofNat 64 len)))
        copyByteWhile)))

/-- **THE BYTE-ADDRESSED BODY COPY.** For a source region holding the bytes `val`
at `[src, src+len)` (`memLoadByte`) and an addressable, non-aliasing destination
region disjoint from the source, running `copySeg dst src len` lays those `len`
bytes at consecutive BYTE addresses `[dst, dst+len)` (read back by `memLoadByte`),
preserving every byte OUTSIDE `[dst, dst+len)` (the frame — so a previously-written
region survives) and `memaddrs`/`be`. This is the packed-byte body copy, the last
word-slot residual of the serialize chain, reproved in the faithful model. -/
theorem copySeg_landsB (o : Oracle σ) (dst src : Word) (val : Nat → BitVec 8) (len : Nat)
    (hlen63 : len < 2 ^ 63)
    (hdisj : ∀ i j, i < len → j < len →
      dst + BitVec.ofNat 64 i ≠ src + BitVec.ofNat 64 j)
    (hinj : ∀ i j, i < len → j < len → i ≠ j →
      dst + BitVec.ofNat 64 i ≠ dst + BitVec.ofNat 64 j)
    (s : PancakeState σ)
    (hclk : len ≤ s.clock)
    (hsrcR : ∀ j, j < len →
      memLoadByte s.memory s.memaddrs s.be (src + BitVec.ofNat 64 j) = some (val j))
    (hdstA : ∀ j, j < len → s.memaddrs (byteAlign (dst + BitVec.ofNat 64 j)) = true) :
    ∃ s', PancakeSem o (copySeg dst src len) s = (none, s')
      ∧ (∀ j, j < len →
          memLoadByte s'.memory s.memaddrs s.be (dst + BitVec.ofNat 64 j) = some (val j))
      ∧ (∀ a, (∀ j, j < len → a ≠ dst + BitVec.ofNat 64 j) →
          memLoadByte s'.memory s.memaddrs s.be a = memLoadByte s.memory s.memaddrs s.be a)
      ∧ s'.memaddrs = s.memaddrs ∧ s'.be = s.be := by
  -- run the four frame-setup assigns
  have hA1 : PancakeSem o (.assign "dst" (.const dst)) s
      = (none, { s with locals := setLocal s.locals "dst" dst }) :=
    sem_assign (oracle := o) (x := "dst") rfl
  let s1 : PancakeState σ := { s with locals := setLocal s.locals "dst" dst }
  have hA2 : PancakeSem o (.assign "src" (.const src)) s1
      = (none, { s1 with locals := setLocal s1.locals "src" src }) :=
    sem_assign (oracle := o) (x := "src") rfl
  let s2 : PancakeState σ := { s1 with locals := setLocal s1.locals "src" src }
  have hA3 : PancakeSem o (.assign "i" (.const (BitVec.ofNat 64 0))) s2
      = (none, { s2 with locals := setLocal s2.locals "i" (BitVec.ofNat 64 0) }) :=
    sem_assign (oracle := o) (x := "i") rfl
  let s3 : PancakeState σ := { s2 with locals := setLocal s2.locals "i" (BitVec.ofNat 64 0) }
  have hA4 : PancakeSem o (.assign "len" (.const (BitVec.ofNat 64 len))) s3
      = (none, { s3 with locals := setLocal s3.locals "len" (BitVec.ofNat 64 len) }) :=
    sem_assign (oracle := o) (x := "len") rfl
  let s4 : PancakeState σ := { s3 with locals := setLocal s3.locals "len" (BitVec.ofNat 64 len) }
  -- field facts for s4
  have hmem4 : s4.memory = s.memory := rfl
  have hma4 : s4.memaddrs = s.memaddrs := rfl
  have hbe4 : s4.be = s.be := rfl
  have hclk4 : s4.clock = s.clock := rfl
  -- locals of s4
  have hdst4 : s4.locals "dst" = some dst := by
    show setLocal (setLocal (setLocal (setLocal s.locals "dst" dst) "src" src) "i"
      (BitVec.ofNat 64 0)) "len" (BitVec.ofNat 64 len) "dst" = some dst
    rw [setLocal_ne _ _ _ (by decide), setLocal_ne _ _ _ (by decide),
        setLocal_ne _ _ _ (by decide), setLocal_same]
  have hsrc4 : s4.locals "src" = some src := by
    show setLocal (setLocal (setLocal (setLocal s.locals "dst" dst) "src" src) "i"
      (BitVec.ofNat 64 0)) "len" (BitVec.ofNat 64 len) "src" = some src
    rw [setLocal_ne _ _ _ (by decide), setLocal_ne _ _ _ (by decide), setLocal_same]
  have hi4 : s4.locals "i" = some (BitVec.ofNat 64 0) := by
    show setLocal (setLocal (setLocal (setLocal s.locals "dst" dst) "src" src) "i"
      (BitVec.ofNat 64 0)) "len" (BitVec.ofNat 64 len) "i" = some (BitVec.ofNat 64 0)
    rw [setLocal_ne _ _ _ (by decide), setLocal_same]
  have hlen4 : s4.locals "len" = some (BitVec.ofNat 64 len) := by
    show setLocal (setLocal (setLocal (setLocal s.locals "dst" dst) "src" src) "i"
      (BitVec.ofNat 64 0)) "len" (BitVec.ofNat 64 len) "len" = some (BitVec.ofNat 64 len)
    rw [setLocal_same]
  -- the entry invariant at index 0 (k = 0)
  have hEntry : copyInvB s.memaddrs s.be s.memory dst src val len len s4 := by
    refine ⟨0, by omega, hma4, hbe4, hdst4, hsrc4, hi4, hlen4, ?_, ?_,
      by intro j hj; omega, ?_⟩
    · intro j hj; rw [hmem4, hma4, hbe4]; exact hsrcR j hj
    · intro j hj; rw [hma4]; exact hdstA j hj
    · intro a _; rw [hmem4, hma4, hbe4]
  -- run the loop
  obtain ⟨s', hs'eq, hs'I, _hs'clk⟩ :=
    while_inv_cond_clk o (.cmp .less (.var "i") (.var "len")) copyByteBody
      (copyInvB s.memaddrs s.be s.memory dst src val len)
      (copyByte_guard s.memaddrs s.be s.memory dst src val len hlen63)
      (copyByte_step o s.memaddrs s.be s.memory dst src val len hlen63 hdisj hinj)
      len s4 hEntry (by rw [hclk4]; exact hclk)
  obtain ⟨k, hk0, hma', hbe', _, _, _, _, _, _, hprog', hfr'⟩ := hs'I
  have hkl : k = len := by omega
  rw [hkl] at hprog' hfr'
  -- assemble copySeg's run
  refine ⟨s', ?_, ?_, ?_, ?_, ?_⟩
  · show PancakeSem o (copySeg dst src len) s = (none, s')
    rw [copySeg]
    rw [seq_step o hA1 (Nat.le_of_eq rfl)]
    rw [seq_step o hA2 (Nat.le_of_eq rfl)]
    rw [seq_step o hA3 (Nat.le_of_eq rfl)]
    rw [seq_step o hA4 (Nat.le_of_eq rfl)]
    exact hs'eq
  · intro j hj; exact hprog' j hj
  · intro a ha; exact hfr' a ha
  · exact hma'
  · exact hbe'

/-! ## 3. Non-vacuity: the loop is `len` byte stores, and a concrete 4-byte copy. -/

-- the body copy is a genuine `While` over `StoreByte`/`LoadByte`, not a stub:
example : copyByteWhile = .while_ (.cmp .less (.var "i") (.var "len"))
  (.seq (.storeByte (.op .add (.var "dst") (.var "i"))
                    (.loadByte (.op .add (.var "src") (.var "i"))))
        (.assign "i" (.op .add (.var "i") (.const (BitVec.ofNat 64 1))))) := rfl

/-! ## 4. Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}, 0 sorryAx. -/

#print axioms copyByte_guard
#print axioms copyByte_step
#print axioms copySeg_landsB

end Pancake.ByteCopy
