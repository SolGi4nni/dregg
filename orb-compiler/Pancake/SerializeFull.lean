/-
  Pancake/SerializeFull.lean — the STRUCTURED response serialization compile:
  the response bytes are materialized into an output region NOT by one flat copy,
  but by a SEQUENCE of per-segment write stages (status line, header block, body),
  composed so that every earlier segment SURVIVES the later writes, landing the
  whole `serialize resp` — status line, header block, blank-line separator, body —
  byte-for-byte into `base_out`.

  This is the scale-up of Pancake/SerializeCompile.lean. That file proved the
  generic write loop `copyWhile` (a bounded memory-write) as ONE `RefinesClk`
  stage (`refinesClk_copy`) and used it to materialize a fully-assembled
  `serialize resp` by a SINGLE flat copy (`serialize_write_correct`). The single
  flat copy is the write-loop PATTERN; the structured build is the SEQUENCE of
  segment writes at running offsets. To compose segment writes the loop needs a
  property `refinesClk_copy` did not carry: a MEMORY FRAME — the loop modifies
  ONLY its own destination region, leaving all other addresses (earlier segments'
  regions, later segments' source regions) untouched. That frame is what this file
  adds and then threads through the composition.

  WHAT IS BUILT (all `#print axioms`-clean, 0 `sorry`, 0 `native_decide`):

   * §1  `copy_stepF` / `copy_loop` — the write loop with EXACT clock accounting
     (`s'.clock = s.clock - len`, needed to thread a budget to a SECOND
     budget-consuming stage — the `≤` accounting of the generic `RefinesClk`
     grammar is insufficient for that, a named finding) PLUS the MEMORY FRAME and
     `memaddrs` preservation: the loop writes `val` on `[0,len)` at `dst` and
     changes NOTHING else.

   * §2  `writeSeg` / `writeSeg_correct` — ONE segment write stage: a 4-assign
     prelude (`dst := base+off; src := srcSeg; i := 0; len := segLen`) that RESETS
     the loop frame, then `copyWhile`. Proven to write `val` on `[0,len)` at
     `base + off`, preserve everything outside that window, preserve `memaddrs`,
     and consume exactly `len` clock. The prelude is what makes a segment write
     re-usable at a new offset with a fresh source.

   * §3  `writeSegs` / `writeSegs_correct` — the STRUCTURED SEQUENCE: a right nest
     of `writeSeg` stages over a LIST of segments at CUMULATIVE offsets, composed
     through the `Seq` semantics with the frame threaded so segment `k`'s bytes
     survive every later segment write. Proven, by induction on the segment list,
     to land `concatSegs segs` (the concatenation of every segment's bytes) into
     `base_out`, given the standard memcpy side conditions (output region
     injective + addressable; each source region loaded + disjoint from the
     output) and the total iteration budget.

   * §4  `serialize_structured_correct` — THE MY-HAND CHECK. Instantiating the
     segment sequence at the THREE pieces of the wire framing — `(statusLine ++
     CRLF)`, `(headerBlock ++ CRLF ++ CRLF)`, `body` — whose concatenation IS
     `serialize resp` (by `serialize_framing`), the structured program lands the
     model memory with the output region at `base_out` equal, byte for byte, to
     `serialize resp` (`MemBytesAt`). The theorem names the real `serialize`; the
     conclusion is a genuine byte-exact memory post-state, not `P → P`.

  natToDec (the decimal render of the status code / content length) is proved
  correct as a bounded DIVIDE-BY-10 digit loop already in
  Pancake/SerializeCompile.lean (`natToDec_readback`: reading the emitted ASCII
  digits back as base-10 recovers `n`). Its instantiation as a real Pancake
  `While` needs `Div`/`Mod` in the modelled expression subset (divide-by-10); the
  subset carries only add/and/sub/mul/cmp/loads (Pancake/Sem.lean), so the digit
  loop lives at the Lean level and the Pancake-`While` form is BLOCKED on
  modelling `Div`/`Mod` — the named sem-foundation primitive dependency.

  RESIDUALS (named, not hidden):
   * The output region is WORD-addressed: byte `i` occupies the word slot at
     `base_out + i` (`wordOfByte`). The PACKED byte layout needs a byte-store
     program primitive (`StoreByte`/`st8`), which the modelled Sem subset does not
     carry (Pancake/Sem.lean lists `storeByte` as an unmodelled constructor) —
     the bytes-lowering residual, shared with SerializeCompile.
   * The header segment is written as a FLAT copy of the pre-rendered header block
     bytes. The further scale-up is the true nested OUTER `While` over the header
     LIST held in memory (each header a variable-length inner copy at a running
     offset), reusing the in-memory list iteration certified in
     Pancake/StructModel.lean (`refinesClk_sumLoop`); its invariant ties "headers
     0..j serialized" to "output prefix written" and is the named next stone.
   * `natToDec` as a real Pancake `While`: BLOCKED on `Div`/`Mod` (above).

  This is Stack L (the Lean model of Pancake) + a memory post-state claim.
-/
import Pancake.SerializeCompile
import Pancake.StructModel

namespace Pancake.SerializeFull

open Pancake Pancake.EmitCorrect Pancake.EmitCorrectCompose Pancake.EmitCorrectLoop
     Pancake.EmitCorrectClock Pancake.SerializeCompile

variable {σ : Type}

/-! ## 0. Address arithmetic + list helpers -/

/-- `getElem!` on a left append prefix. -/
theorem bytes_append_left (bs cr : Bytes) (i : Nat) (h : i < bs.length) :
    (bs ++ cr)[i]! = bs[i]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD, List.getElem?_append_left h]

/-- `getElem!` on a right append suffix. -/
theorem bytes_append_right (bs cr : Bytes) (i : Nat) (h : bs.length ≤ i) :
    (bs ++ cr)[i]! = cr[i - bs.length]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD, List.getElem?_append_right h]


/-- `x < 2^63 → x < 2^64`. -/
theorem lt_pow64_of_lt_pow63 {x : Nat} (h : x < 2 ^ 63) : x < 2 ^ 64 :=
  Nat.lt_trans h (Nat.pow_lt_pow_right (by omega) (by omega))

/-- Splitting an offset address: `(base + off) + j = base + (off + j)` in the
64-bit word ring, when the summed offset is in range. -/
theorem seg_addr (base : Word) (off j : Nat) (h : off + j < 2 ^ 64) :
    base + BitVec.ofNat 64 off + BitVec.ofNat 64 j = base + BitVec.ofNat 64 (off + j) := by
  rw [BitVec.add_assoc, ofNat_add_small off j h]

/-- A sequence `Seq (Assign x e) rest` whose RHS `e` evaluates to `v`: the `Seq`
clock-clamp is a no-op (assign preserves clock), so it reduces to running `rest`
on the updated state. The reusable prelude-composition step. -/
theorem sem_assign_seq (o : Oracle σ) (x : String) (e : PancakeExp) (v : Value)
    (rest : PancakeProg) {s : PancakeState σ} (hv : eval s e = some v) :
    PancakeSem o (.seq (.assign x e) rest) s
      = PancakeSem o rest { s with locals := setLocal s.locals x v } := by
  rw [sem_seq_none (oracle := o) (sem_assign (oracle := o) hv)]
  congr 1
  have hc : (({ s with locals := setLocal s.locals x v } : PancakeState σ).clock) = s.clock := rfl
  rw [hc, Nat.min_self]

/-! ## 1. The write loop with EXACT clock + a MEMORY FRAME

`copy_stepF` re-proves the single write iteration of `SerializeCompile.copyBody`,
exposing — beyond the invariant advance — that the step touches memory at EXACTLY
the one destination slot it writes (`memaddrs` unchanged; every non-target address
preserved). `copy_loop` lifts that to the whole `copyWhile`, delivering the
written region, the frame, `memaddrs` preservation, and the EXACT residual clock. -/

/-- ONE write iteration, with the frame exposed. Mirrors
`SerializeCompile.copy_step` and additionally returns: `memaddrs` unchanged, and
every address outside the destination region preserved. -/
theorem copy_stepF (o : Oracle σ) (dst src : Word) (val : Nat → Word) (len : Nat)
    (hlen63 : len < 2 ^ 63)
    (hdisj : ∀ i j, i < len → j < len →
      dst + BitVec.ofNat 64 i ≠ src + BitVec.ofNat 64 j)
    (hinj : ∀ i j, i < len → j < len → i ≠ j →
      dst + BitVec.ofNat 64 i ≠ dst + BitVec.ofNat 64 j)
    (n : Nat) (s : PancakeState σ) (hI : copyInv dst src val len (n + 1) s) :
    ∃ s2, PancakeSem o copyBody (decClock s) = (none, s2) ∧
      copyInv dst src val len n s2 ∧ s2.clock = s.clock - 1 ∧
      (∀ a, s2.memaddrs a = s.memaddrs a) ∧
      (∀ a, (∀ j, j < len → a ≠ dst + BitVec.ofNat 64 j) → s2.memory a = s.memory a) := by
  obtain ⟨k, hkn, hdst, hsrc, hi, hlen, hsrcR, hdstA, hprog⟩ := hI
  have hklt : k < len := by omega
  have hdl : (decClock s).locals = s.locals := rfl
  have haddr : eval (decClock s) (.op .add (.var "dst") (.var "i"))
      = some (dst + BitVec.ofNat 64 k) := by
    simp only [eval, hdl, hdst, hi]
  have hsrcAddr : eval (decClock s) (.op .add (.var "src") (.var "i"))
      = some (src + BitVec.ofNat 64 k) := by
    simp only [eval, hdl, hsrc, hi]
  have hload : eval (decClock s) (.loadWord (.op .add (.var "src") (.var "i")))
      = some (val k) := by
    have hma : (decClock s).memaddrs (src + BitVec.ofNat 64 k) = true := (hsrcR k hklt).1
    have hmv : (decClock s).memory (src + BitVec.ofNat 64 k) = val k := (hsrcR k hklt).2
    show (match eval (decClock s) (.op .add (.var "src") (.var "i")) with
          | some w => if (decClock s).memaddrs w then some ((decClock s).memory w) else none
          | none => none) = _
    rw [hsrcAddr]
    simp only [hma, hmv, if_true]
  have hinS : (decClock s).memaddrs (dst + BitVec.ofNat 64 k) = true := hdstA k hklt
  obtain ⟨sS, hsS⟩ : ∃ sS : PancakeState σ,
      sS = { (decClock s) with memory :=
              fun x => if x = dst + BitVec.ofNat 64 k then val k else (decClock s).memory x } := ⟨_, rfl⟩
  have hstore : PancakeSem o (.store (.op .add (.var "dst") (.var "i"))
        (.loadWord (.op .add (.var "src") (.var "i")))) (decClock s) = (none, sS) := by
    rw [sem_store o haddr hload hinS, ← hsS]
  have hiE : eval sS (.op .add (.var "i") (.const (BitVec.ofNat 64 1)))
      = some (BitVec.ofNat 64 (k + 1)) := by
    have hsSi : sS.locals "i" = some (BitVec.ofNat 64 k) := by rw [hsS]; exact hi
    show (match eval sS (.var "i"), eval sS (.const (BitVec.ofNat 64 1)) with
          | some x, some y => some (x + y) | _, _ => none) = _
    simp only [eval, hsSi]
    rw [ofNat_add_small _ _ (by omega)]
  obtain ⟨sB, hsB⟩ : ∃ sB : PancakeState σ,
      sB = { sS with locals := setLocal sS.locals "i" (BitVec.ofNat 64 (k + 1)) } := ⟨_, rfl⟩
  have hbump := sem_assign (oracle := o) (x := "i") hiE
  rw [← hsB] at hbump
  have hclkSS : sS.clock = (decClock s).clock := by rw [hsS]
  have hclamp : ({ sS with clock := min (decClock s).clock sS.clock } : PancakeState σ) = sS := by
    rw [hclkSS, Nat.min_self, ← hclkSS]
  have hbody : PancakeSem o copyBody (decClock s) = (none, sB) := by
    rw [copyBody, sem_seq_none hstore, hclamp, hbump]
  have dne1 : ("dst" = "i") = False := by decide
  have dne2 : ("src" = "i") = False := by decide
  have dne3 : ("len" = "i") = False := by decide
  have hBdst : sB.locals "dst" = some dst := by
    rw [hsB]; simp only [setLocal, dne1, if_false]; rw [hsS]; exact hdst
  have hBsrc : sB.locals "src" = some src := by
    rw [hsB]; simp only [setLocal, dne2, if_false]; rw [hsS]; exact hsrc
  have hBi : sB.locals "i" = some (BitVec.ofNat 64 (k + 1)) := by
    rw [hsB]; simp only [setLocal, if_true]
  have hBlen : sB.locals "len" = some (BitVec.ofNat 64 len) := by
    rw [hsB]; simp only [setLocal, dne3, if_false]; rw [hsS]; exact hlen
  have hBmem : sB.memory
      = fun x => if x = dst + BitVec.ofNat 64 k then val k else s.memory x := by
    rw [hsB, hsS]; rfl
  have hBma : ∀ x, sB.memaddrs x = s.memaddrs x := by
    intro x; rw [hsB, hsS]; rfl
  have hBsrcR : ∀ j, j < len → sB.memaddrs (src + BitVec.ofNat 64 j) = true ∧
                     sB.memory (src + BitVec.ofNat 64 j) = val j := by
    intro j hj
    refine ⟨by rw [hBma]; exact (hsrcR j hj).1, ?_⟩
    simp only [hBmem]
    rw [if_neg (fun h => hdisj k j hklt hj h.symm)]
    exact (hsrcR j hj).2
  have hBdstA : ∀ j, j < len → sB.memaddrs (dst + BitVec.ofNat 64 j) = true := by
    intro j hj; rw [hBma]; exact hdstA j hj
  have hBprog : ∀ j, j < k + 1 → sB.memory (dst + BitVec.ofNat 64 j) = val j := by
    intro j hj
    simp only [hBmem]
    by_cases hjk : j = k
    · subst hjk; simp
    · rw [if_neg (fun h => hinj j k (by omega) hklt hjk h)]
      exact hprog j (by omega)
  have hBclk : sB.clock = s.clock - 1 := by rw [hsB, hsS]; simp [decClock]
  -- the frame: an address outside the whole destination region is untouched
  have hBframe : ∀ a, (∀ j, j < len → a ≠ dst + BitVec.ofNat 64 j) → sB.memory a = s.memory a := by
    intro a ha
    simp only [hBmem]
    rw [if_neg (ha k hklt)]
  exact ⟨sB, hbody, ⟨k + 1, by omega, hBdst, hBsrc, hBi, hBlen, hBsrcR, hBdstA, hBprog⟩,
         hBclk, hBma, hBframe⟩

/-- The write loop `copyWhile` run to completion, with EXACT clock and the frame.
From `copyInv … rem s` with budget `rem ≤ s.clock`, `copyWhile` reaches `copyInv …
0 s'` (destination region holds `val` on `[0,len)`), having consumed EXACTLY `rem`
clock, preserved `memaddrs`, and left every address outside the destination region
untouched. Direct induction on `rem` over `copy_stepF`. -/
theorem copy_loop (o : Oracle σ) (dst src : Word) (val : Nat → Word) (len : Nat)
    (hlen63 : len < 2 ^ 63)
    (hdisj : ∀ i j, i < len → j < len →
      dst + BitVec.ofNat 64 i ≠ src + BitVec.ofNat 64 j)
    (hinj : ∀ i j, i < len → j < len → i ≠ j →
      dst + BitVec.ofNat 64 i ≠ dst + BitVec.ofNat 64 j) :
    ∀ (rem : Nat) (s : PancakeState σ), copyInv dst src val len rem s → rem ≤ s.clock →
      ∃ s', PancakeSem o copyWhile s = (none, s') ∧ copyInv dst src val len 0 s'
        ∧ s'.clock = s.clock - rem
        ∧ (∀ a, s'.memaddrs a = s.memaddrs a)
        ∧ (∀ a, (∀ j, j < len → a ≠ dst + BitVec.ofNat 64 j) → s'.memory a = s.memory a) := by
  intro rem
  induction rem with
  | zero =>
    intro s hI _
    refine ⟨s, ?_, hI, by omega, fun _ => rfl, fun _ _ => rfl⟩
    rw [copyWhile, PancakeSem, copy_guard dst src val len hlen63 0 s hI]; simp
  | succ m ih =>
    intro s hI hclock
    have hclock0 : s.clock ≠ 0 := by omega
    have hcond : eval s (.cmp .less (.var "i") (.var "len")) = some (1 : Word) := by
      have := copy_guard dst src val len hlen63 (m + 1) s hI; simpa using this
    obtain ⟨s2, hs2eq, hs2I, hs2clk, hs2ma, hs2frame⟩ :=
      copy_stepF o dst src val len hlen63 hdisj hinj m s hI
    have hmin : min (s.clock - 1) s2.clock = s2.clock := by omega
    have hclamp : ({ s2 with clock := min (s.clock - 1) s2.clock } : PancakeState σ) = s2 := by
      rw [hmin]
    obtain ⟨s', hs'eq, hs'I, hs'clk, hs'ma, hs'frame⟩ := ih s2 hs2I (by omega)
    refine ⟨s', ?_, hs'I, by omega, ?_, ?_⟩
    · rw [copyWhile, PancakeSem]
      simp only [hcond, ne_eq, show ((1 : Word) = 0) = False from by decide, not_false_eq_true,
                 if_true, hclock0, if_false, clampClock, hs2eq]
      rw [hclamp]
      have := hs'eq; rw [copyWhile] at this; exact this
    · intro a; rw [hs'ma a, hs2ma a]
    · intro a ha; rw [hs'frame a ha, hs2frame a ha]

/-! ## 2. One segment write stage -/

/-- One segment write: reset the loop frame to `(dst := base+off, src := srcSeg,
i := 0, len := segLen)`, then run the write loop. The 4-assign prelude is what
makes the loop reusable at a fresh offset with a fresh source, so segments compose
into a sequence. -/
def writeSeg (base : Word) (off : Nat) (srcSeg : Word) (len : Nat) : PancakeProg :=
  .seq (.assign "dst" (.const (base + BitVec.ofNat 64 off)))
   (.seq (.assign "src" (.const srcSeg))
    (.seq (.assign "i" (.const (BitVec.ofNat 64 0)))
     (.seq (.assign "len" (.const (BitVec.ofNat 64 len))) copyWhile)))

/-- ONE segment write is correct: given the source region loaded with `val`, the
destination window `[base+off, base+off+len)` addressable, injective, and disjoint
from the source, the stage writes `val` into that window, preserves every other
address, preserves `memaddrs`, and consumes exactly `len` clock. -/
theorem writeSeg_correct (o : Oracle σ) (base : Word) (off : Nat) (srcSeg : Word)
    (val : Nat → Word) (len : Nat) (s : PancakeState σ)
    (hoff63 : off + len < 2 ^ 63)
    (hsrc : ∀ j, j < len → s.memaddrs (srcSeg + BitVec.ofNat 64 j) = true ∧
                          s.memory (srcSeg + BitVec.ofNat 64 j) = val j)
    (hdstA : ∀ j, j < len → s.memaddrs (base + BitVec.ofNat 64 (off + j)) = true)
    (hinj : ∀ j j', j < len → j' < len → j ≠ j' →
      base + BitVec.ofNat 64 (off + j) ≠ base + BitVec.ofNat 64 (off + j'))
    (hdisj : ∀ j j', j < len → j' < len →
      base + BitVec.ofNat 64 (off + j) ≠ srcSeg + BitVec.ofNat 64 j')
    (hclock : len ≤ s.clock) :
    ∃ s', PancakeSem o (writeSeg base off srcSeg len) s = (none, s')
      ∧ (∀ j, j < len → s'.memory (base + BitVec.ofNat 64 (off + j)) = val j)
      ∧ (∀ a, (∀ j, j < len → a ≠ base + BitVec.ofNat 64 (off + j)) → s'.memory a = s.memory a)
      ∧ (∀ a, s'.memaddrs a = s.memaddrs a)
      ∧ s'.clock = s.clock - len := by
  -- the pre-copy state (prelude ran): the four loop-frame locals set
  obtain ⟨s4, hs4def⟩ : ∃ s4 : PancakeState σ, s4 = { s with locals := setLocal (setLocal (setLocal (setLocal s.locals "dst" (base + BitVec.ofNat 64 off)) "src" srcSeg) "i" (BitVec.ofNat 64 0)) "len" (BitVec.ofNat 64 len) } := ⟨_, rfl⟩
  -- the prelude reduces the program to `copyWhile` on `s4`
  have hprelude : PancakeSem o (writeSeg base off srcSeg len) s = PancakeSem o copyWhile s4 := by
    rw [hs4def, writeSeg,
        sem_assign_seq o "dst" (.const (base + BitVec.ofNat 64 off)) (base + BitVec.ofNat 64 off) _ rfl,
        sem_assign_seq o "src" (.const srcSeg) srcSeg _ rfl,
        sem_assign_seq o "i" (.const (BitVec.ofNat 64 0)) (BitVec.ofNat 64 0) _ rfl,
        sem_assign_seq o "len" (.const (BitVec.ofNat 64 len)) (BitVec.ofNat 64 len) _ rfl]
  have hlen63 : len < 2 ^ 63 := by omega
  -- address split: within-window destination addresses are `(base+off)+j`
  have hbridge : ∀ j, j < len →
      base + BitVec.ofNat 64 off + BitVec.ofNat 64 j = base + BitVec.ofNat 64 (off + j) := by
    intro j hj; exact seg_addr base off j (lt_pow64_of_lt_pow63 (by omega))
  -- copy hypotheses in `(base+off)`-relative form
  have hdisj' : ∀ i j, i < len → j < len →
      base + BitVec.ofNat 64 off + BitVec.ofNat 64 i ≠ srcSeg + BitVec.ofNat 64 j := by
    intro i j hi hj; rw [hbridge i hi]; exact hdisj i j hi hj
  have hinj' : ∀ i j, i < len → j < len → i ≠ j →
      base + BitVec.ofNat 64 off + BitVec.ofNat 64 i ≠ base + BitVec.ofNat 64 off + BitVec.ofNat 64 j := by
    intro i j hi hj hne; rw [hbridge i hi, hbridge j hj]; exact hinj i j hi hj hne
  -- the entry invariant on `s4`
  have hs4dst : s4.locals "dst" = some (base + BitVec.ofNat 64 off) := by
    rw [hs4def]; simp [setLocal]
  have hs4src : s4.locals "src" = some srcSeg := by rw [hs4def]; simp [setLocal]
  have hs4i : s4.locals "i" = some (BitVec.ofNat 64 0) := by rw [hs4def]; simp [setLocal]
  have hs4len : s4.locals "len" = some (BitVec.ofNat 64 len) := by rw [hs4def]; simp [setLocal]
  have hs4mem : ∀ a, s4.memory a = s.memory a := by intro a; rw [hs4def]
  have hs4ma : ∀ a, s4.memaddrs a = s.memaddrs a := by intro a; rw [hs4def]
  have hs4clk : s4.clock = s.clock := by rw [hs4def]
  have hentry : copyInv (base + BitVec.ofNat 64 off) srcSeg val len len s4 := by
    refine ⟨0, by omega, hs4dst, hs4src, hs4i, hs4len, ?_, ?_, ?_⟩
    · intro j hj
      refine ⟨by rw [hs4ma]; exact (hsrc j hj).1, by rw [hs4mem]; exact (hsrc j hj).2⟩
    · intro j hj; rw [hs4ma, hbridge j hj]; exact hdstA j hj
    · intro j hj; omega
  obtain ⟨s', hs'eq, hs'I, hs'clk, hs'ma, hs'frame⟩ :=
    copy_loop o (base + BitVec.ofNat 64 off) srcSeg val len hlen63 hdisj' hinj'
      len s4 hentry (by rw [hs4clk]; exact hclock)
  -- read off the written region from `copyInv 0`
  obtain ⟨kf, hkf, _, _, _, _, _, _, hprogf⟩ := hs'I
  have hkflen : kf = len := by omega
  subst hkflen
  refine ⟨s', by rw [hprelude]; exact hs'eq, ?_, ?_, ?_, ?_⟩
  · intro j hj; rw [← hbridge j hj]; exact hprogf j hj
  · intro a ha
    rw [hs'frame a ?_, hs4mem a]
    intro j hj; rw [hbridge j hj]; exact ha j hj
  · intro a; rw [hs'ma a, hs4ma a]
  · rw [hs'clk, hs4clk]

/-! ## 3. The structured segment SEQUENCE -/

/-- A segment: its source base pointer and the bytes it carries. -/
abbrev Seg := Word × Bytes

/-- Total byte count of a segment list. -/
def totalLen : List Seg → Nat
  | []            => 0
  | (_, bs) :: rest => bs.length + totalLen rest

/-- Concatenation of every segment's bytes, in order. -/
def concatSegs : List Seg → Bytes
  | []            => []
  | (_, bs) :: rest => bs ++ concatSegs rest

theorem concat_len : ∀ segs : List Seg, (concatSegs segs).length = totalLen segs
  | []            => rfl
  | (_, bs) :: rest => by
    simp only [concatSegs, totalLen, List.length_append, concat_len rest]

/-- The structured program: the right nest of per-segment writes at CUMULATIVE
offsets (`off` for the head, `off + headLen` for the tail). -/
def writeSegs (base : Word) : Nat → List Seg → PancakeProg
  | _, []               => .skip
  | off, (sr, bs) :: rest =>
      .seq (writeSeg base off sr bs.length) (writeSegs base (off + bs.length) rest)

/-- Every remaining segment's source region is loaded with the `wordOfByte` image
of its bytes AND is disjoint from the whole output region `[base, base+N)`. -/
def SourcesOK (base : Word) (N : Nat) : List Seg → PancakeState σ → Prop
  | [], _               => True
  | (sr, bs) :: rest, s =>
      (∀ j, j < bs.length → s.memaddrs (sr + BitVec.ofNat 64 j) = true ∧
                            s.memory (sr + BitVec.ofNat 64 j) = wordOfByte bs[j]!) ∧
      (∀ j p, j < bs.length → p < N →
        sr + BitVec.ofNat 64 j ≠ base + BitVec.ofNat 64 p) ∧
      SourcesOK base N rest s

/-- `SourcesOK` transports across a write that only changed the window
`[base+off, base+off+len)` (and left `memaddrs` alone): every remaining source is
disjoint from the whole output region, hence from that window, so its loaded bytes
survive. -/
theorem SourcesOK_frame (base : Word) (N off len : Nat) (hle : off + len ≤ N)
    {s s1 : PancakeState σ}
    (hma : ∀ a, s1.memaddrs a = s.memaddrs a)
    (hframe : ∀ a, (∀ j, j < len → a ≠ base + BitVec.ofNat 64 (off + j)) → s1.memory a = s.memory a) :
    ∀ segs : List Seg, SourcesOK base N segs s → SourcesOK base N segs s1
  | [], _ => trivial
  | (sr, bs) :: rest, hS => by
    obtain ⟨hload, hdisjS, hrest⟩ := hS
    refine ⟨?_, hdisjS, SourcesOK_frame base N off len hle hma hframe rest hrest⟩
    intro j hj
    refine ⟨by rw [hma]; exact (hload j hj).1, ?_⟩
    rw [hframe (sr + BitVec.ofNat 64 j) ?_]
    · exact (hload j hj).2
    · intro i hi
      exact hdisjS j (off + i) hj (by omega)

/-- **THE STRUCTURED SEQUENCE IS CORRECT.** Running the right nest of per-segment
writes lands `concatSegs segs` (the concatenation of every segment's bytes) into
the output region at `base + off`, given: the output region `[base, base+N)` is
injective and addressable, every source region is loaded and disjoint from the
output (`SourcesOK`), the offsets fit (`off + totalLen segs ≤ N < 2^63`), and the
total budget is available. It ALSO reports the frame outside the written span,
`memaddrs` preservation, and the exact residual clock — the accounting each outer
step needs to admit the next. Induction on the segment list; each cons composes
one `writeSeg_correct` with the tail through the `Seq` semantics, threading the
frame so the head's bytes survive every later write. -/
theorem writeSegs_correct (o : Oracle σ) (base : Word) (N : Nat) (hN : N < 2 ^ 63)
    (hOinj : ∀ p q, p < N → q < N →
      base + BitVec.ofNat 64 p = base + BitVec.ofNat 64 q → p = q) :
    ∀ (segs : List Seg) (off : Nat) (s : PancakeState σ),
      off + totalLen segs ≤ N →
      (∀ p, p < N → s.memaddrs (base + BitVec.ofNat 64 p) = true) →
      SourcesOK base N segs s →
      totalLen segs ≤ s.clock →
      ∃ s', PancakeSem o (writeSegs base off segs) s = (none, s')
        ∧ (∀ i, i < (concatSegs segs).length →
              s'.memory (base + BitVec.ofNat 64 (off + i)) = wordOfByte (concatSegs segs)[i]!)
        ∧ (∀ a, (∀ i, i < totalLen segs → a ≠ base + BitVec.ofNat 64 (off + i)) →
              s'.memory a = s.memory a)
        ∧ (∀ a, s'.memaddrs a = s.memaddrs a)
        ∧ s'.clock = s.clock - totalLen segs := by
  intro segs
  induction segs with
  | nil =>
    intro off s _ _ _ _
    refine ⟨s, ?_, ?_, ?_, fun _ => rfl, ?_⟩
    · show PancakeSem o PancakeProg.skip s = (none, s); rw [PancakeSem]
    · intro i hi; simp [concatSegs] at hi
    · intro a _; rfl
    · simp [totalLen]
  | cons hd rest ih =>
    obtain ⟨sr, bs⟩ := hd
    intro off s hbound hOaddr hSrc hclk
    let len := bs.length
    have hT : totalLen ((sr, bs) :: rest) = len + totalLen rest := rfl
    obtain ⟨hload, hdisjS, hrestS⟩ := hSrc
    -- STEP 1: write the head segment `bs` at offset `off`
    have hoff63 : off + len < 2 ^ 63 := by
      have : off + len ≤ N := by rw [hT] at hbound; omega
      omega
    obtain ⟨s1, hrun1, hreg1, hframe1, hma1, hclk1⟩ :=
      writeSeg_correct o base off sr (fun j => wordOfByte bs[j]!) len s hoff63
        hload
        (by intro j hj; exact hOaddr (off + j) (by rw [hT] at hbound; omega))
        (by intro j j' hj hj' hne h
            have := hOinj (off + j) (off + j')
              (by rw [hT] at hbound; omega) (by rw [hT] at hbound; omega) h
            omega)
        (by intro j j' hj hj'
            exact (hdisjS j' (off + j) hj' (by rw [hT] at hbound; omega)).symm)
        (by rw [hT] at hclk; omega)
    -- STEP 2: recurse on `rest` at offset `off + len`, on state `s1`
    have hbound' : (off + len) + totalLen rest ≤ N := by rw [hT] at hbound; omega
    have hOaddr' : ∀ p, p < N → s1.memaddrs (base + BitVec.ofNat 64 p) = true := by
      intro p hp; rw [hma1]; exact hOaddr p hp
    have hSrc' : SourcesOK base N rest s1 :=
      SourcesOK_frame base N off len (by rw [hT] at hbound; omega) hma1 hframe1 rest hrestS
    have hclk1' : s1.clock = s.clock - len := hclk1
    have hclkrest : totalLen rest ≤ s1.clock := by rw [hclk1']; rw [hT] at hclk; omega
    obtain ⟨s', hrun', hreg', hframe', hma', hclk'⟩ :=
      ih (off + len) s1 hbound' hOaddr' hSrc' hclkrest
    -- ASSEMBLE
    have hs1le : s1.clock ≤ s.clock := by rw [hclk1']; omega
    refine ⟨s', ?_, ?_, ?_, ?_, ?_⟩
    · -- the sequence reduces through the head then the tail
      show PancakeSem o (.seq (writeSeg base off sr len) (writeSegs base (off + len) rest)) s = _
      rw [sem_seq_none (oracle := o) hrun1]
      have hmin : min s.clock s1.clock = s1.clock := by omega
      rw [show ({ s1 with clock := min s.clock s1.clock } : PancakeState σ) = s1 from by rw [hmin]]
      exact hrun'
    · -- the written region: head bytes then tail bytes
      intro i hi
      rw [concatSegs] at hi ⊢
      have hlensplit : (bs ++ concatSegs rest).length = len + (concatSegs rest).length := by
        rw [List.length_append]
      by_cases hilt : i < len
      · -- head byte: survives the tail write (outside the tail window)
        have hval : (bs ++ concatSegs rest)[i]! = bs[i]! := bytes_append_left bs _ i hilt
        rw [hval]
        have hne : ∀ i', i' < totalLen rest →
            base + BitVec.ofNat 64 (off + i) ≠ base + BitVec.ofNat 64 ((off + len) + i') := by
          intro i' hi'
          intro h
          have hpq := hOinj (off + i) ((off + len) + i')
            (by rw [hT] at hbound; omega) (by rw [hT] at hbound; omega) h
          omega
        rw [hframe' (base + BitVec.ofNat 64 (off + i)) hne]
        exact hreg1 i hilt
      · -- tail byte: written by the recursion
        have hile : len ≤ i := by omega
        have hval : (bs ++ concatSegs rest)[i]! = (concatSegs rest)[i - len]! :=
          bytes_append_right bs _ i hile
        rw [hval]
        have hi2 : i - len < (concatSegs rest).length := by
          rw [hlensplit] at hi; omega
        have := hreg' (i - len) hi2
        have heq : (off + len) + (i - len) = off + i := by omega
        rw [heq] at this
        exact this
    · -- frame: outside the whole written span
      intro a ha
      rw [hT] at ha
      rw [hframe' a ?_, hframe1 a ?_]
      · intro j hj
        have := ha j (by omega)
        exact this
      · intro i' hi'
        have := ha (len + i') (by omega)
        have heq : off + (len + i') = (off + len) + i' := by omega
        rw [heq] at this
        exact this
    · intro a; rw [hma' a, hma1 a]
    · rw [hclk', hclk1', hT]; omega

/-! ## 4. `serialize_structured_correct` — the response materialized, structured -/

/-- The status-line segment: `HTTP/1.1 SP status SP reason` + CRLF. -/
def statusSeg (resp : Response) : Bytes := statusLineOf resp ++ crlf

/-- The header segment: the rendered header block + the blank-line separator. -/
def headerSeg (resp : Response) : Bytes := headerBlockOf resp ++ crlf ++ crlf

/-- The three segments of the response wire image, in order. -/
def respSegs (resp : Response) (srcS srcH srcB : Word) : List Seg :=
  [(srcS, statusSeg resp), (srcH, headerSeg resp), (srcB, resp.body)]

/-- Their concatenation is exactly `serialize resp` (by `serialize_framing`). -/
theorem concat_respSegs (resp : Response) (srcS srcH srcB : Word) :
    concatSegs (respSegs resp srcS srcH srcB) = serialize resp := by
  rw [serialize_framing]
  simp only [respSegs, concatSegs, statusSeg, headerSeg, List.append_nil, List.append_assoc]

/-- **THE MY-HAND CHECK.** The structured program — status-line write, then header
segment write, then body copy, at cumulative offsets — lands the model memory with
the output region at `base_out` equal, byte for byte, to `serialize resp`
(`MemBytesAt`). Side conditions are exactly a segmented memcpy's: the output region
fits the signed range and is injective/addressable, and each source region holds
its segment's bytes disjoint from the output (`SourcesOK`); plus the total
iteration budget. The conclusion names the real `serialize` and is a genuine
byte-exact memory post-state. -/
theorem serialize_structured_correct (o : Oracle σ) (resp : Response)
    (base_out srcS srcH srcB : Word) (s : PancakeState σ)
    (hN : (serialize resp).length < 2 ^ 63)
    (hOinj : ∀ p q, p < (serialize resp).length → q < (serialize resp).length →
      base_out + BitVec.ofNat 64 p = base_out + BitVec.ofNat 64 q → p = q)
    (hOaddr : ∀ p, p < (serialize resp).length →
      s.memaddrs (base_out + BitVec.ofNat 64 p) = true)
    (hSrc : SourcesOK base_out (serialize resp).length (respSegs resp srcS srcH srcB) s)
    (hclock : (serialize resp).length ≤ s.clock) :
    ∃ s', PancakeSem o (writeSegs base_out 0 (respSegs resp srcS srcH srcB)) s = (none, s')
      ∧ MemBytesAt s' base_out (serialize resp) := by
  have hci : concatSegs (respSegs resp srcS srcH srcB) = serialize resp :=
    concat_respSegs resp srcS srcH srcB
  have hlen : totalLen (respSegs resp srcS srcH srcB) = (serialize resp).length := by
    rw [← hci, concat_len]
  obtain ⟨s', hrun, hreg, _, _, _⟩ :=
    writeSegs_correct o base_out (serialize resp).length hN hOinj
      (respSegs resp srcS srcH srcB) 0 s
      (by rw [hlen]; omega)
      hOaddr hSrc (by rw [hlen]; exact hclock)
  refine ⟨s', hrun, ?_⟩
  intro i hi
  have hi' : i < (concatSegs (respSegs resp srcS srcH srcB)).length := by rw [hci]; exact hi
  have := hreg i hi'
  rw [hci] at this
  simpa using this

/-! ## 5. Non-vacuity of the structured reconstruction

The concatenation of the three segments IS `serialize resp` — checked on the real
`sampleResp` (a `200 OK` with one caller header and a 2-byte body): the segment
decomposition is a genuine, non-trivial split of the 48 serialized bytes, and the
intended output values are the serialized bytes in their word slots. So
`serialize_structured_correct`'s conclusion is a real memory relation, not `P → P`.
-/

#guard concatSegs (respSegs sampleResp 0 0 0) = serialize sampleResp
#guard (statusSeg sampleResp).length = 17   -- `HTTP/1.1 200 OK` + CRLF
#guard (headerSeg sampleResp).length = 29   -- two header lines + CRLF + CRLF
#guard sampleResp.body.length = 2
#guard (statusSeg sampleResp).length + (headerSeg sampleResp).length + sampleResp.body.length = 48
#guard totalLen (respSegs sampleResp 0 0 0) = 48
-- the segments are non-empty and distinct (a real three-way split):
#guard (statusSeg sampleResp) ≠ (headerSeg sampleResp)
#guard (concatSegs (respSegs sampleResp 0 0 0)).map (·.toNat)
       = (serialize sampleResp).map (·.toNat)

/-! ### natToDec — the decimal render, as a bounded divide-by-10 loop

`natToDec` and its correctness (`natToDec_readback`: the emitted ASCII digits read
back as base-10 recover `n`, i.e. it emits the decimal digits of `n`) are proved
in Pancake/SerializeCompile.lean. Re-exposed here as the digit renderer the status
line and Content-Length use. Its instantiation as a real Pancake `While` is blocked
on `Div`/`Mod` in the modelled expression subset — the named sem-foundation dep. -/

theorem natToDec_readback' (n : Nat) : readFrom 0 (natToDec n) = n := natToDec_readback n

#guard natToDec sampleResp.status = [50, 48, 48]   -- "200"
#guard natToDec (serialize sampleResp).length = [52, 56]   -- "48"

/-! ## 6. Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}, 0 sorryAx. -/

#print axioms copy_stepF
#print axioms copy_loop
#print axioms writeSeg_correct
#print axioms writeSegs_correct
#print axioms serialize_structured_correct

end Pancake.SerializeFull
