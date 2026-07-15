/-
  Pancake/SerializeHeaders.lean — the NESTED-HEADER serialize: the header block is
  materialized NOT by a single flat copy of pre-rendered bytes, but by a genuine
  OUTER `While` over the header LIST held in memory, each header a variable-length
  INNER copy loop `copyWhile` at a running output offset. This closes the named
  residual of Pancake/SerializeFull.lean (its header segment is a flat copy) and of
  Pancake/SerializeCompile.lean (the scale-up to a per-header outer loop).

  THE SHAPE. A header/segment array lives in memory: record `k` at `recPtr k` holds
  two words — the segment's source byte base and its byte length — followed (in a
  disjoint region) by the segment's bytes. The compiled program is

      j := 0; off := 0; p := recPtr 0;
      while (j < count) {
        dst := obase + off;             -- output cursor
        src := load p;                  -- this segment's source base
        i   := 0;
        len := load (p + 8);            -- this segment's byte length
        while (i < len) {               -- INNER COPY (copyWhile)
          store (dst + i) (load (src + i)); i := i + 1
        }
        off := off + len;               -- advance the output cursor
        p   := p + 32;                  -- advance to the next record
        j   := j + 1
      }

  and it lands `concatSegs segs` (the concatenation of every segment's bytes) into
  the output region prefix `[obase, obase + Σ len)`.

  WHAT IS BUILT (all `#print axioms`-clean, 0 `sorry`, 0 `native_decide`):

   * §1  The inner copy's LOCALS FRAME. `copyWhile` writes only local `i` and the
     destination memory — every OTHER local (`j`, `count`, `off`, `p`, `obase`)
     survives it. `while_inv_cond_clk` / `copy_loop` deliver the memory effect but
     not this locals frame, and the outer loop's guard/postlude read exactly those
     surviving locals AFTER the inner copy, so the frame is required. Proved by a
     clock induction over the `While`, resting on `copyBody`'s store+assign form.

   * §2  The OUTER loop. `segInv` is the outer invariant: `j` segments processed,
     `off = Σ_{k<j} len k`, and the output prefix holds `concatSegs (take j)`;
     `segStep` advances it across one iteration (a prelude, the inner copy via
     `copy_loop`, and a postlude), threading the memcpy frame so the already-written
     prefix, the record array, and the remaining sources all survive; `segLoop`
     runs the outer `While` to completion (`j = count`). Each outer iteration
     consumes `1 + len j` clock, so the uniform one-tick `while_inv_cond_clk` does
     NOT apply — the outer induction is bespoke, carrying the byte budget.

   * §3  `segLoop_membytes` — the per-segment postcondition lifted to
     `MemBytesAt obase (concatSegs segs)` via the concatenation-indexing lemma.

   * §4  Instantiation at a Response's header lines: each header renders to the
     segment `name ": " value CRLF`, and the concatenation of those segments is the
     header block plus the blank-line separator — so EVERY header written by the
     outer loop appears in the serialized bytes (`header_seg_framing`).

  This is Stack L (the Lean model of Pancake) + a memory post-state claim; the same
  word-addressed output model and residuals as SerializeFull (byte-packing needs a
  `StoreByte` primitive; `natToDec` needs `Div`/`Mod`).
-/
import Pancake.SerializeFull

namespace Pancake.SerializeHeaders

open Pancake Pancake.EmitCorrect Pancake.EmitCorrectLoop Pancake.EmitCorrectClock
     Pancake.SerializeCompile Pancake.SerializeFull

variable {σ : Type}

/-! ## 1. The inner copy's LOCALS FRAME

`copyWhile` mutates only local `i` (per iteration) and the destination memory. The
outer loop reads its own locals (`j`, `count`, `off`, `p`, `obase`) AFTER the inner
copy — to re-test the guard and run the postlude — so we need that those survive
the inner `While`. `copy_loop` reports the memory effect and `memaddrs`, but not the
locals frame; we establish it here by a clock induction over `copyWhile`, resting on
the store+assign form of `copyBody`. -/

/-- A `Store` run terminates with `none` (a successful in-range store) or `some
.error` (an out-of-range / ill-typed store) — never a control result. -/
theorem store_form (o : Oracle σ) (a b : PancakeExp) (s : PancakeState σ) :
    (PancakeSem o (.store a b) s).1 = none ∨ (PancakeSem o (.store a b) s).1 = some .error := by
  rw [PancakeSem]
  split
  · split
    · exact Or.inl rfl
    · exact Or.inr rfl
  · exact Or.inr rfl

/-- A successful `Store` leaves every local untouched (it writes memory only). -/
theorem store_locals (o : Oracle σ) {a b : PancakeExp} {s s2 : PancakeState σ}
    (h : PancakeSem o (.store a b) s = (none, s2)) : s2.locals = s.locals := by
  rw [PancakeSem] at h
  split at h
  · split at h
    · rw [Prod.mk.injEq] at h; rw [← h.2]
    · simp at h
  · simp at h

/-- A successful `Assign v e` leaves every local OTHER than `v` untouched. -/
theorem assign_locals_ne (o : Oracle σ) {v : String} {e : PancakeExp} {s s2 : PancakeState σ}
    (h : PancakeSem o (.assign v e) s = (none, s2)) {x : String} (hx : x ≠ v) :
    s2.locals x = s.locals x := by
  rw [PancakeSem] at h
  cases he : eval s e with
  | none => rw [he] at h; simp at h
  | some val =>
    rw [he] at h
    rw [Prod.mk.injEq] at h
    rw [← h.2]
    simp only [setLocal, hx, if_false]

/-- `Seq c1 c2` inversion for a normal termination: `c1` ran normally to `s1`, then
`c2` ran on the clock-clamped `s1` to the final state. -/
theorem seq_none_inv (o : Oracle σ) {c1 c2 : PancakeProg} {s s' : PancakeState σ}
    (h : PancakeSem o (.seq c1 c2) s = (none, s')) :
    ∃ s1, PancakeSem o c1 s = (none, s1) ∧
      PancakeSem o c2 { s1 with clock := min s.clock s1.clock } = (none, s') := by
  rw [PancakeSem] at h
  cases hp : PancakeSem o c1 s with
  | mk res s1 =>
    rw [hp] at h
    simp only [clampClock] at h
    cases res with
    | none => exact ⟨s1, rfl, h⟩
    | some r => simp at h

/-- `copyBody` (`store; i := i+1`) leaves every local other than `i` untouched. -/
theorem copyBody_locals (o : Oracle σ) {s s' : PancakeState σ}
    (h : PancakeSem o copyBody s = (none, s')) {x : String} (hx : x ≠ "i") :
    s'.locals x = s.locals x := by
  rw [copyBody] at h
  obtain ⟨s1, hstore, hbump⟩ := seq_none_inv o h
  have h1 : s1.locals = s.locals := store_locals o hstore
  have h2 := assign_locals_ne o hbump hx
  rw [h2]
  show s1.locals x = s.locals x
  rw [h1]

/-- `copyBody` terminates with `none` or `some .error` — never a control result.
This lets the outer `While`'s continue/break arms be discharged. -/
theorem copyBody_form (o : Oracle σ) (s : PancakeState σ) :
    (PancakeSem o copyBody s).1 = none ∨ (PancakeSem o copyBody s).1 = some .error := by
  rw [copyBody, PancakeSem]
  cases hst : PancakeSem o (PancakeProg.store (.op .add (.var "dst") (.var "i"))
      (.loadWord (.op .add (.var "src") (.var "i")))) s with
  | mk r1 s1 =>
    simp only [clampClock]
    cases r1 with
    | none =>
      simp only []
      rw [PancakeSem]
      cases eval { s1 with clock := min s.clock s1.clock }
          (.op .add (.var "i") (.const (BitVec.ofNat 64 1))) with
      | none => right; rfl
      | some v => left; rfl
    | some res =>
      have hf := store_form o (.op .add (.var "dst") (.var "i"))
        (.loadWord (.op .add (.var "src") (.var "i"))) s
      rw [hst] at hf
      exact hf

/-- **THE INNER-COPY LOCALS FRAME.** From any state, whenever `copyWhile` runs to a
normal termination, every local OTHER than `i` is preserved. Clock induction over
the `While`: each iteration runs `copyBody` (which preserves `x ≠ i`) then recurses
on a strictly smaller clock; the exit and time-out cases are immediate. -/
theorem copyWhile_locals (o : Oracle σ) {x : String} (hx : x ≠ "i") :
    ∀ (n : Nat) (s s' : PancakeState σ), s.clock ≤ n →
      PancakeSem o copyWhile s = (none, s') → s'.locals x = s.locals x := by
  intro n
  induction n with
  | zero =>
    intro s s' hcn h
    have hc0 : s.clock = 0 := by omega
    rw [copyWhile, PancakeSem] at h
    cases hg : eval s (.cmp .less (.var "i") (.var "len")) with
    | none => simp only [hg] at h; simp at h
    | some w =>
      simp only [hg] at h
      by_cases hw : w ≠ 0
      · rw [if_pos hw, if_pos hc0] at h; simp at h
      · rw [if_neg hw] at h
        rw [Prod.mk.injEq] at h
        rw [← h.2]
  | succ m ih =>
    intro s s' hcn h
    rw [copyWhile, PancakeSem] at h
    cases hg : eval s (.cmp .less (.var "i") (.var "len")) with
    | none => simp only [hg] at h; simp at h
    | some w =>
      simp only [hg] at h
      by_cases hw : w ≠ 0
      · rw [if_pos hw] at h
        by_cases hc0 : s.clock = 0
        · rw [if_pos hc0] at h; simp at h
        · rw [if_neg hc0] at h
          cases hpb : PancakeSem o copyBody (decClock s) with
          | mk res sb =>
            rw [hpb] at h
            simp only [clampClock] at h
            have hform := copyBody_form o (decClock s)
            rw [hpb] at hform
            simp only at hform
            rcases hform with rfl | rfl
            · -- res = none: recurse on the clock-clamped body state
              simp only [] at h
              have hsb : sb.locals x = s.locals x := by
                have := copyBody_locals o hpb hx
                simpa [decClock] using this
              have hclk2 : (min (s.clock - 1) sb.clock) ≤ m := by omega
              have hrec := ih { sb with clock := min (s.clock - 1) sb.clock } s' hclk2 h
              rw [hrec]
              exact hsb
            · -- res = some .error: the `some res` arm gives `(some .error, _)`, contra
              simp at h
      · rw [if_neg hw] at h
        rw [Prod.mk.injEq] at h
        rw [← h.2]

/-! ## 2. The OUTER loop over the in-memory segment array -/

/-- Record-word offsets (source-base at `+0`, length at `+8`); record stride 32. -/
def w8  : Word := BitVec.ofNat 64 8
def w32 : Word := BitVec.ofNat 64 32

/-- Cumulative byte offset of segment `k`: `Σ_{i<k} slen i`. -/
def psum (f : Nat → Nat) : Nat → Nat
  | 0     => 0
  | k + 1 => psum f k + f k

theorem psum_le (f : Nat → Nat) : ∀ {a b : Nat}, a ≤ b → psum f a ≤ psum f b := by
  intro a b h
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (Nat.le_add_right _ _)

/-- The outer loop body: set the output cursor + this segment's source/len from its
in-memory record, run the INNER copy (`copyWhile`), then advance the cursor, record
pointer, and segment index. -/
def segBody : PancakeProg :=
  .seq (.assign "dst" (.op .add (.var "obase") (.var "off")))
   (.seq (.assign "src" (.loadWord (.var "p")))
    (.seq (.assign "i" (.const (BitVec.ofNat 64 0)))
     (.seq (.assign "len" (.loadWord (.op .add (.var "p") (.const w8))))
      (.seq copyWhile
       (.seq (.assign "off" (.op .add (.var "off") (.var "len")))
        (.seq (.assign "p" (.op .add (.var "p") (.const w32)))
              (.assign "j" (.op .add (.var "j") (.const (BitVec.ofNat 64 1))))))))))

/-- The outer `While (j < count)`. -/
def segWhile : PancakeProg :=
  .while_ (.cmp .less (.var "j") (.var "count")) segBody

/-- THE OUTER INVARIANT (with `n` segments still to write, `j = count - n`
processed): the loop locals; the record array + all source regions intact
(read-only across the loop); the output region addressable; the output prefix
holding segments `0..j` at their cumulative offsets; and the byte+iteration budget
`n + (N - psum slen j) ≤ clock`. -/
def segInv (count : Nat) (recPtr sbase : Nat → Word) (slen : Nat → Nat)
    (val : Nat → Nat → Word) (obase : Word) (N : Nat)
    (n : Nat) (s : PancakeState σ) : Prop :=
  ∃ j, j + n = count ∧
    s.locals "j"     = some (BitVec.ofNat 64 j) ∧
    s.locals "count" = some (BitVec.ofNat 64 count) ∧
    s.locals "off"   = some (BitVec.ofNat 64 (psum slen j)) ∧
    s.locals "p"     = some (recPtr j) ∧
    s.locals "obase" = some obase ∧
    (∀ k, k < count → s.memaddrs (recPtr k) = true ∧ s.memory (recPtr k) = sbase k ∧
                      s.memaddrs (recPtr k + w8) = true ∧
                      s.memory (recPtr k + w8) = BitVec.ofNat 64 (slen k)) ∧
    (∀ k m, k < count → m < slen k →
        s.memaddrs (sbase k + BitVec.ofNat 64 m) = true ∧
        s.memory (sbase k + BitVec.ofNat 64 m) = val k m) ∧
    (∀ q, q < N → s.memaddrs (obase + BitVec.ofNat 64 q) = true) ∧
    (∀ k m, k < j → m < slen k →
        s.memory (obase + BitVec.ofNat 64 (psum slen k + m)) = val k m) ∧
    n + (N - psum slen j) ≤ s.clock

/-- The outer guard `j < count` is `0` exactly when the walk is done (`n = 0`). -/
theorem segGuard (count : Nat) (recPtr sbase : Nat → Word) (slen : Nat → Nat)
    (val : Nat → Nat → Word) (obase : Word) (N : Nat) (hcount63 : count < 2 ^ 63)
    (n : Nat) (s : PancakeState σ) (hI : segInv count recPtr sbase slen val obase N n s) :
    eval s (.cmp .less (.var "j") (.var "count")) = some (if n = 0 then (0 : Word) else 1) := by
  obtain ⟨j, hjn, hj, hcount, _⟩ := hI
  have hj63 : j < 2 ^ 63 := by omega
  have hev : eval s (.cmp .less (.var "j") (.var "count"))
      = some (if signedLt (BitVec.ofNat 64 j) (BitVec.ofNat 64 count) then 1 else 0) := by
    simp only [eval, hj, hcount]
  rw [hev, signedLt_ofNat j count hj63 hcount63]
  by_cases hn : n = 0
  · have : j = count := by omega
    subst this; simp [hn]
  · have : j < count := by omega
    simp [hn, this]

/-- `eval` of `Load One (Var nm)` from a `nm`-pointer to a mapped word. -/
theorem eval_load_var {s : PancakeState σ} {nm : String} {a v : Word}
    (hp : s.locals nm = some a) (hma : s.memaddrs a = true) (hmem : s.memory a = v) :
    eval s (.loadWord (.var nm)) = some v := by
  show (match eval s (.var nm) with
        | some w => if s.memaddrs w then some (s.memory w) else none | none => none) = _
  simp only [eval, hp, hma, hmem, if_true]

/-- `eval` of `Load One (Var nm + off)` from a `nm`-pointer to a mapped word. -/
theorem eval_load_off {s : PancakeState σ} {nm : String} {a v off : Word}
    (hp : s.locals nm = some a) (hma : s.memaddrs (a + off) = true)
    (hmem : s.memory (a + off) = v) :
    eval s (.loadWord (.op .add (.var nm) (.const off))) = some v := by
  have haddr : eval s (.op .add (.var nm) (.const off)) = some (a + off) := by
    simp only [eval, hp]
  show (match eval s (.op .add (.var nm) (.const off)) with
        | some w => if s.memaddrs w then some (s.memory w) else none | none => none) = _
  rw [haddr]; simp only [hma, hmem, if_true]

/-- **ONE OUTER ITERATION.** From `segInv (n+1)` (segment `j` next), running
`segBody` on `decClock s` writes segment `j`'s bytes into the output at offset
`psum slen j` (via the inner `copyWhile`), advances the cursor / record pointer /
index, and lands `segInv n`. The prelude sets the loop frame from the record;
`copy_loop` does the write with its memcpy frame; `copyWhile_locals` carries the
outer locals across; the frame threads the earlier prefix, the record array, and
the remaining sources safely past the write. -/
theorem segStep (o : Oracle σ) (count : Nat) (recPtr sbase : Nat → Word) (slen : Nat → Nat)
    (val : Nat → Nat → Word) (obase : Word) (N : Nat)
    (hcount63 : count < 2 ^ 63) (hN63 : N < 2 ^ 63)
    (hfit : ∀ k, k < count → psum slen k + slen k ≤ N)
    (hOinj : ∀ p q, p < N → q < N →
        obase + BitVec.ofNat 64 p = obase + BitVec.ofNat 64 q → p = q)
    (hOS : ∀ k m q, k < count → m < slen k → q < N →
        sbase k + BitVec.ofNat 64 m ≠ obase + BitVec.ofNat 64 q)
    (hOR : ∀ k q, k < count → q < N →
        recPtr k ≠ obase + BitVec.ofNat 64 q ∧ recPtr k + w8 ≠ obase + BitVec.ofNat 64 q)
    (hstep : ∀ k, recPtr (k + 1) = recPtr k + w32)
    (n : Nat) (s : PancakeState σ)
    (hI : segInv count recPtr sbase slen val obase N (n + 1) s) :
    ∃ s2, PancakeSem o segBody (decClock s) = (none, s2) ∧
      segInv count recPtr sbase slen val obase N n s2 ∧ s2.clock ≤ s.clock - 1 := by
  obtain ⟨j, hjn, hj, hcount, hoff, hp, hobase, hrec, hsrc, hOaddr, hpref, hbud⟩ := hI
  have hjc : j < count := by omega
  have hfitj : psum slen j + slen j ≤ N := hfit j hjc
  have hlen63 : slen j < 2 ^ 63 := by omega
  -- address split within the output window
  have hbridge : ∀ m, m < slen j →
      obase + BitVec.ofNat 64 (psum slen j) + BitVec.ofNat 64 m
        = obase + BitVec.ofNat 64 (psum slen j + m) := by
    intro m hm; exact seg_addr obase (psum slen j) m (lt_pow64_of_lt_pow63 (by omega))
  -- the prelude-updated state (dst/src/i/len set from the record)
  obtain ⟨s4, hs4def⟩ : ∃ s4 : PancakeState σ,
      s4 = { (decClock s) with locals := setLocal (setLocal (setLocal (setLocal (decClock s).locals "dst" (obase + BitVec.ofNat 64 (psum slen j))) "src" (sbase j)) "i" (BitVec.ofNat 64 0)) "len" (BitVec.ofNat 64 (slen j)) } := ⟨_, rfl⟩
  have hs4mem : ∀ a, s4.memory a = s.memory a := by intro a; simp [hs4def, decClock]
  have hs4ma : ∀ a, s4.memaddrs a = s.memaddrs a := by intro a; simp [hs4def, decClock]
  have hs4clk : s4.clock = s.clock - 1 := by simp [hs4def, decClock]
  -- prelude eval facts
  have e1 : eval (decClock s) (.op .add (.var "obase") (.var "off"))
      = some (obase + BitVec.ofNat 64 (psum slen j)) := by
    have ho : (decClock s).locals "obase" = some obase := hobase
    have hf : (decClock s).locals "off" = some (BitVec.ofNat 64 (psum slen j)) := hoff
    simp only [eval, ho, hf]
  have e2 : eval { (decClock s) with locals := setLocal (decClock s).locals "dst" (obase + BitVec.ofNat 64 (psum slen j)) } (.loadWord (.var "p")) = some (sbase j) := by
    apply eval_load_var
    · show setLocal (decClock s).locals "dst" (obase + BitVec.ofNat 64 (psum slen j)) "p" = some (recPtr j)
      simp only [setLocal]; rw [if_neg (by decide)]; exact hp
    · show (decClock s).memaddrs (recPtr j) = true; exact (hrec j hjc).1
    · show (decClock s).memory (recPtr j) = sbase j; exact (hrec j hjc).2.1
  have e3 : ∀ st : PancakeState σ, eval st (.const (BitVec.ofNat 64 0)) = some (BitVec.ofNat 64 0) :=
    fun _ => rfl
  have e4 : eval { (decClock s) with locals := setLocal (setLocal (setLocal (decClock s).locals "dst" (obase + BitVec.ofNat 64 (psum slen j))) "src" (sbase j)) "i" (BitVec.ofNat 64 0) } (.loadWord (.op .add (.var "p") (.const w8))) = some (BitVec.ofNat 64 (slen j)) := by
    apply eval_load_off
    · show setLocal (setLocal (setLocal (decClock s).locals "dst" (obase + BitVec.ofNat 64 (psum slen j))) "src" (sbase j)) "i" (BitVec.ofNat 64 0) "p" = some (recPtr j)
      simp only [setLocal]; rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]; exact hp
    · show (decClock s).memaddrs (recPtr j + w8) = true; exact (hrec j hjc).2.2.1
    · show (decClock s).memory (recPtr j + w8) = BitVec.ofNat 64 (slen j); exact (hrec j hjc).2.2.2
  -- the prelude reduces `segBody` to `copyWhile ; postlude` on `s4`
  have hprelude : PancakeSem o segBody (decClock s)
      = PancakeSem o (.seq copyWhile
          (.seq (.assign "off" (.op .add (.var "off") (.var "len")))
           (.seq (.assign "p" (.op .add (.var "p") (.const w32)))
                 (.assign "j" (.op .add (.var "j") (.const (BitVec.ofNat 64 1))))))) s4 := by
    rw [hs4def, segBody,
        sem_assign_seq (o := o) (x := "dst") (hv := e1),
        sem_assign_seq (o := o) (x := "src") (hv := e2),
        sem_assign_seq (o := o) (x := "i") (hv := e3 _),
        sem_assign_seq (o := o) (x := "len") (hv := e4)]
  -- inner copy set-up
  have hdisjC : ∀ i' m', i' < slen j → m' < slen j →
      obase + BitVec.ofNat 64 (psum slen j) + BitVec.ofNat 64 i' ≠ sbase j + BitVec.ofNat 64 m' := by
    intro i' m' hi' hm'; rw [hbridge i' hi']
    exact (hOS j m' (psum slen j + i') hjc hm' (by omega)).symm
  have hinjC : ∀ i' m', i' < slen j → m' < slen j → i' ≠ m' →
      obase + BitVec.ofNat 64 (psum slen j) + BitVec.ofNat 64 i'
        ≠ obase + BitVec.ofNat 64 (psum slen j) + BitVec.ofNat 64 m' := by
    intro i' m' hi' hm' hne; rw [hbridge i' hi', hbridge m' hm']
    intro heq; have := hOinj (psum slen j + i') (psum slen j + m') (by omega) (by omega) heq; omega
  have hentry : copyInv (obase + BitVec.ofNat 64 (psum slen j)) (sbase j) (fun m => val j m)
      (slen j) (slen j) s4 := by
    refine ⟨0, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show s4.locals "dst" = some _; rw [hs4def]; simp [setLocal]
    · show s4.locals "src" = some _; rw [hs4def]; simp [setLocal]
    · show s4.locals "i" = some _; rw [hs4def]; simp [setLocal]
    · show s4.locals "len" = some _; rw [hs4def]; simp [setLocal]
    · intro m hm
      exact ⟨by rw [hs4ma]; exact (hsrc j m hjc hm).1, by rw [hs4mem]; exact (hsrc j m hjc hm).2⟩
    · intro m hm; rw [hs4ma, hbridge m hm]; exact hOaddr (psum slen j + m) (by omega)
    · intro m hm; omega
  have hbudC : slen j ≤ s4.clock := by rw [hs4clk]; omega
  obtain ⟨s5, hs5eq, hs5I, hs5clk, hs5ma, hs5frame⟩ :=
    copy_loop o (obase + BitVec.ofNat 64 (psum slen j)) (sbase j) (fun m => val j m)
      (slen j) hlen63 hdisjC hinjC (slen j) s4 hentry hbudC
  obtain ⟨kf, hkf, _, _, _, _, _, _, hs5prog⟩ := hs5I
  have hkflen : kf = slen j := by omega
  subst hkflen
  -- outer locals survive the inner copy
  have hs5loc : ∀ x, x ≠ "i" → s5.locals x = s4.locals x :=
    fun x hx => copyWhile_locals o hx s4.clock s4 s5 (Nat.le_refl _) hs5eq
  have hs4other : ∀ x, x ≠ "dst" → x ≠ "src" → x ≠ "i" → x ≠ "len" → s4.locals x = s.locals x := by
    intro x hd hsr hi hl; rw [hs4def]; simp only [setLocal]
    rw [if_neg hl, if_neg hi, if_neg hsr, if_neg hd]; rfl
  have hs5off : s5.locals "off" = some (BitVec.ofNat 64 (psum slen j)) := by
    rw [hs5loc "off" (by decide), hs4other "off" (by decide) (by decide) (by decide) (by decide)]; exact hoff
  have hs5p : s5.locals "p" = some (recPtr j) := by
    rw [hs5loc "p" (by decide), hs4other "p" (by decide) (by decide) (by decide) (by decide)]; exact hp
  have hs5j : s5.locals "j" = some (BitVec.ofNat 64 j) := by
    rw [hs5loc "j" (by decide), hs4other "j" (by decide) (by decide) (by decide) (by decide)]; exact hj
  have hs5count : s5.locals "count" = some (BitVec.ofNat 64 count) := by
    rw [hs5loc "count" (by decide), hs4other "count" (by decide) (by decide) (by decide) (by decide)]; exact hcount
  have hs5obase : s5.locals "obase" = some obase := by
    rw [hs5loc "obase" (by decide), hs4other "obase" (by decide) (by decide) (by decide) (by decide)]; exact hobase
  have hs4len : s4.locals "len" = some (BitVec.ofNat 64 (slen j)) := by rw [hs4def]; simp [setLocal]
  have hs5len : s5.locals "len" = some (BitVec.ofNat 64 (slen j)) := by
    rw [hs5loc "len" (by decide)]; exact hs4len
  -- postlude states + evals
  obtain ⟨t1, ht1⟩ : ∃ t1 : PancakeState σ,
      t1 = { s5 with locals := setLocal s5.locals "off" (BitVec.ofNat 64 (psum slen j + slen j)) } := ⟨_, rfl⟩
  have ep : eval t1 (.op .add (.var "p") (.const w32)) = some (recPtr (j + 1)) := by
    have hpT1 : t1.locals "p" = some (recPtr j) := by
      rw [ht1]; simp only [setLocal]; rw [if_neg (by decide)]; exact hs5p
    simp only [eval, hpT1]; rw [← hstep j]
  obtain ⟨t2, ht2⟩ : ∃ t2 : PancakeState σ,
      t2 = { t1 with locals := setLocal t1.locals "p" (recPtr (j + 1)) } := ⟨_, rfl⟩
  have ej : eval t2 (.op .add (.var "j") (.const (BitVec.ofNat 64 1)))
      = some (BitVec.ofNat 64 (j + 1)) := by
    have hjT2 : t2.locals "j" = some (BitVec.ofNat 64 j) := by
      rw [ht2]; simp only [setLocal]; rw [if_neg (by decide)]
      rw [ht1]; simp only [setLocal]; rw [if_neg (by decide)]; exact hs5j
    simp only [eval, hjT2]; rw [ofNat_add_small j 1 (by omega)]
  have eoff : eval s5 (.op .add (.var "off") (.var "len"))
      = some (BitVec.ofNat 64 (psum slen j + slen j)) := by
    simp only [eval, hs5off, hs5len]; rw [ofNat_add_small _ _ (by omega)]
  obtain ⟨s2, hs2def⟩ : ∃ s2 : PancakeState σ,
      s2 = { t2 with locals := setLocal t2.locals "j" (BitVec.ofNat 64 (j + 1)) } := ⟨_, rfl⟩
  have hclampS5 : ({ s5 with clock := min s4.clock s5.clock } : PancakeState σ) = s5 := by
    rw [show min s4.clock s5.clock = s5.clock from by rw [hs5clk]; omega]
  have hbody : PancakeSem o segBody (decClock s) = (none, s2) := by
    rw [hprelude, sem_seq_none (oracle := o) hs5eq, hclampS5,
        sem_assign_seq (o := o) (x := "off") (hv := eoff), ← ht1,
        sem_assign_seq (o := o) (x := "p") (hv := ep), ← ht2,
        sem_assign (oracle := o) ej, ← hs2def]
  -- memory / clock of s2
  have hmemS2 : ∀ a, s2.memory a = s5.memory a := by intro a; simp only [hs2def, ht2, ht1]
  have hmaS2 : ∀ a, s2.memaddrs a = s5.memaddrs a := by intro a; simp only [hs2def, ht2, ht1]
  have hclkS2 : s2.clock = s5.clock := by simp only [hs2def, ht2, ht1]
  have hclkval : s2.clock = s.clock - 1 - slen j := by rw [hclkS2, hs5clk, hs4clk]
  -- memory outside the just-written window is preserved from `s`
  have hmemOut : ∀ a, (∀ m, m < slen j →
        a ≠ obase + BitVec.ofNat 64 (psum slen j) + BitVec.ofNat 64 m) →
      s5.memory a = s.memory a := by
    intro a ha; rw [hs5frame a ha, hs4mem a]
  have hmaS2S : ∀ a, s2.memaddrs a = s.memaddrs a := by
    intro a; rw [hmaS2 a, hs5ma a, hs4ma a]
  -- s2 locals (other than j/p/off unchanged from s5)
  have hs2other : ∀ x, x ≠ "j" → x ≠ "p" → x ≠ "off" → s2.locals x = s5.locals x := by
    intro x hxj hxp hxoff
    rw [hs2def]; simp only [setLocal]; rw [if_neg hxj]
    rw [ht2]; simp only [setLocal]; rw [if_neg hxp]
    rw [ht1]; simp only [setLocal]; rw [if_neg hxoff]
  refine ⟨s2, hbody, ⟨j + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by omega⟩
  · -- j
    rw [hs2def]; simp [setLocal]
  · -- count
    rw [hs2other "count" (by decide) (by decide) (by decide)]; exact hs5count
  · -- off  (psum slen (j+1) = psum slen j + slen j)
    show s2.locals "off" = some (BitVec.ofNat 64 (psum slen j + slen j))
    rw [hs2def]; simp only [setLocal]; rw [if_neg (by decide)]
    rw [ht2]; simp only [setLocal]; rw [if_neg (by decide)]
    rw [ht1]; simp [setLocal]
  · -- p
    rw [hs2def]; simp only [setLocal]; rw [if_neg (by decide)]
    rw [ht2]; simp [setLocal]
  · -- obase
    rw [hs2other "obase" (by decide) (by decide) (by decide)]; exact hs5obase
  · -- records preserved
    intro k hk
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hmaS2S]; exact (hrec k hk).1
    · rw [hmemS2, hmemOut (recPtr k)
        (by intro m hm; rw [hbridge m hm]; exact (hOR k (psum slen j + m) hk (by omega)).1)]
      exact (hrec k hk).2.1
    · rw [hmaS2S]; exact (hrec k hk).2.2.1
    · rw [hmemS2, hmemOut (recPtr k + w8)
        (by intro m hm; rw [hbridge m hm]; exact (hOR k (psum slen j + m) hk (by omega)).2)]
      exact (hrec k hk).2.2.2
  · -- sources preserved
    intro k m hk hm
    refine ⟨?_, ?_⟩
    · rw [hmaS2S]; exact (hsrc k m hk hm).1
    · rw [hmemS2, hmemOut (sbase k + BitVec.ofNat 64 m)
        (by intro m' hm'; rw [hbridge m' hm']; exact hOS k m (psum slen j + m') hk hm (by omega))]
      exact (hsrc k m hk hm).2
  · -- output addressable
    intro q hq; rw [hmaS2S]; exact hOaddr q hq
  · -- written prefix (0..j+1)
    intro k m hk hm
    by_cases hkj : k < j
    · -- earlier segment survives the write
      rw [hmemS2, hmemOut (obase + BitVec.ofNat 64 (psum slen k + m))
        (by
          intro m' hm'
          rw [hbridge m' hm']
          intro heq
          have hlt : psum slen k + m < psum slen j := by
            have h1 : psum slen (k + 1) ≤ psum slen j := psum_le slen (by omega)
            have h2 : psum slen k + m < psum slen (k + 1) := by
              show psum slen k + m < psum slen k + slen k; omega
            omega
          have := hOinj (psum slen k + m) (psum slen j + m') (by omega) (by omega) heq
          omega)]
      exact hpref k m hkj hm
    · -- current segment j: freshly written by the inner copy
      have hkeq : k = j := by omega
      subst hkeq
      rw [hmemS2, ← hbridge m hm]
      exact hs5prog m hm
  · -- budget
    rw [hclkval, show psum slen (j + 1) = psum slen j + slen j from rfl]; omega

/-! ## 3. The outer loop run to completion -/

/-- **THE OUTER LOOP IS CORRECT.** From `segInv n` (with the budget in the
invariant) the outer `segWhile` runs to `segInv 0` — every segment `0..count`
written into the output at its cumulative offset. Bespoke induction on `n`,
composing `segStep` through the `While` semantics (each iteration consumes
`1 + slen j` clock, so this is NOT the uniform one-tick rule). -/
theorem segLoop (o : Oracle σ) (count : Nat) (recPtr sbase : Nat → Word) (slen : Nat → Nat)
    (val : Nat → Nat → Word) (obase : Word) (N : Nat)
    (hcount63 : count < 2 ^ 63) (hN63 : N < 2 ^ 63)
    (hfit : ∀ k, k < count → psum slen k + slen k ≤ N)
    (hOinj : ∀ p q, p < N → q < N →
        obase + BitVec.ofNat 64 p = obase + BitVec.ofNat 64 q → p = q)
    (hOS : ∀ k m q, k < count → m < slen k → q < N →
        sbase k + BitVec.ofNat 64 m ≠ obase + BitVec.ofNat 64 q)
    (hOR : ∀ k q, k < count → q < N →
        recPtr k ≠ obase + BitVec.ofNat 64 q ∧ recPtr k + w8 ≠ obase + BitVec.ofNat 64 q)
    (hstep : ∀ k, recPtr (k + 1) = recPtr k + w32) :
    ∀ (n : Nat) (s : PancakeState σ), segInv count recPtr sbase slen val obase N n s →
      ∃ s', PancakeSem o segWhile s = (none, s') ∧ segInv count recPtr sbase slen val obase N 0 s' := by
  intro n
  induction n with
  | zero =>
    intro s hI
    refine ⟨s, ?_, hI⟩
    rw [segWhile, PancakeSem, segGuard count recPtr sbase slen val obase N hcount63 0 s hI]; simp
  | succ m ih =>
    intro s hI
    obtain ⟨s2, hs2eq, hs2I, hs2clk⟩ :=
      segStep o count recPtr sbase slen val obase N hcount63 hN63 hfit hOinj hOS hOR hstep m s hI
    have hcond : eval s (.cmp .less (.var "j") (.var "count")) = some (1 : Word) := by
      have := segGuard count recPtr sbase slen val obase N hcount63 (m + 1) s hI; simpa using this
    have hclock0 : s.clock ≠ 0 := by
      obtain ⟨j, hjn, _, _, _, _, _, _, _, _, _, hbud⟩ := hI; omega
    obtain ⟨s', hs'eq, hs'I⟩ := ih s2 hs2I
    refine ⟨s', ?_, hs'I⟩
    rw [segWhile, PancakeSem]
    simp only [hcond, ne_eq, show ((1 : Word) = 0) = False from by decide, not_false_eq_true,
               if_true, hclock0, if_false, clampClock, hs2eq]
    rw [show ({ s2 with clock := min (s.clock - 1) s2.clock } : PancakeState σ) = s2 from by
      rw [show min (s.clock - 1) s2.clock = s2.clock from by omega]]
    exact hs'eq

/-- The entry invariant from the canonical loop start (`j = 0`, `off = 0`,
`p = recPtr 0`, no prefix written yet), the record array + sources loaded, the
output addressable, and the total byte+iteration budget `count + N ≤ clock`. -/
theorem segInv_entry (count : Nat) (recPtr sbase : Nat → Word) (slen : Nat → Nat)
    (val : Nat → Nat → Word) (obase : Word) (N : Nat) (s : PancakeState σ)
    (hj : s.locals "j" = some (BitVec.ofNat 64 0))
    (hcount : s.locals "count" = some (BitVec.ofNat 64 count))
    (hoff : s.locals "off" = some (BitVec.ofNat 64 0))
    (hp : s.locals "p" = some (recPtr 0))
    (hobase : s.locals "obase" = some obase)
    (hrec : ∀ k, k < count → s.memaddrs (recPtr k) = true ∧ s.memory (recPtr k) = sbase k ∧
                s.memaddrs (recPtr k + w8) = true ∧ s.memory (recPtr k + w8) = BitVec.ofNat 64 (slen k))
    (hsrc : ∀ k m, k < count → m < slen k → s.memaddrs (sbase k + BitVec.ofNat 64 m) = true ∧
                s.memory (sbase k + BitVec.ofNat 64 m) = val k m)
    (hOaddr : ∀ q, q < N → s.memaddrs (obase + BitVec.ofNat 64 q) = true)
    (hclock : count + N ≤ s.clock) :
    segInv count recPtr sbase slen val obase N count s := by
  refine ⟨0, by omega, hj, hcount, ?_, hp, hobase, hrec, hsrc, hOaddr, ?_, ?_⟩
  · simpa [psum] using hoff
  · intro k m hk _; exact absurd hk (Nat.not_lt_zero k)
  · simp only [psum]; omega

/-- **THE NESTED-HEADER SERIALIZE (per-segment form).** From the canonical entry,
the OUTER `segWhile` runs to completion and lands EVERY segment `k`'s bytes at its
cumulative offset `psum slen k` in the output region — the genuine outer loop over
the in-memory segment (header) array, not a flat copy. -/
theorem segWhile_writes (o : Oracle σ) (count : Nat) (recPtr sbase : Nat → Word)
    (slen : Nat → Nat) (val : Nat → Nat → Word) (obase : Word) (N : Nat)
    (hcount63 : count < 2 ^ 63) (hN63 : N < 2 ^ 63)
    (hfit : ∀ k, k < count → psum slen k + slen k ≤ N)
    (hOinj : ∀ p q, p < N → q < N →
        obase + BitVec.ofNat 64 p = obase + BitVec.ofNat 64 q → p = q)
    (hOS : ∀ k m q, k < count → m < slen k → q < N →
        sbase k + BitVec.ofNat 64 m ≠ obase + BitVec.ofNat 64 q)
    (hOR : ∀ k q, k < count → q < N →
        recPtr k ≠ obase + BitVec.ofNat 64 q ∧ recPtr k + w8 ≠ obase + BitVec.ofNat 64 q)
    (hstep : ∀ k, recPtr (k + 1) = recPtr k + w32)
    (s : PancakeState σ)
    (hj : s.locals "j" = some (BitVec.ofNat 64 0))
    (hcount : s.locals "count" = some (BitVec.ofNat 64 count))
    (hoff : s.locals "off" = some (BitVec.ofNat 64 0))
    (hp : s.locals "p" = some (recPtr 0))
    (hobase : s.locals "obase" = some obase)
    (hrec : ∀ k, k < count → s.memaddrs (recPtr k) = true ∧ s.memory (recPtr k) = sbase k ∧
                s.memaddrs (recPtr k + w8) = true ∧ s.memory (recPtr k + w8) = BitVec.ofNat 64 (slen k))
    (hsrc : ∀ k m, k < count → m < slen k → s.memaddrs (sbase k + BitVec.ofNat 64 m) = true ∧
                s.memory (sbase k + BitVec.ofNat 64 m) = val k m)
    (hOaddr : ∀ q, q < N → s.memaddrs (obase + BitVec.ofNat 64 q) = true)
    (hclock : count + N ≤ s.clock) :
    ∃ s', PancakeSem o segWhile s = (none, s') ∧
      ∀ k m, k < count → m < slen k →
        s'.memory (obase + BitVec.ofNat 64 (psum slen k + m)) = val k m := by
  have hI := segInv_entry count recPtr sbase slen val obase N s hj hcount hoff hp hobase
    hrec hsrc hOaddr hclock
  obtain ⟨s', hs'eq, hs'I⟩ :=
    segLoop o count recPtr sbase slen val obase N hcount63 hN63 hfit hOinj hOS hOR hstep count s hI
  obtain ⟨jf, hjf, _, _, _, _, _, _, _, _, hpref, _⟩ := hs'I
  have hjfc : jf = count := by omega
  subst hjfc
  exact ⟨s', hs'eq, hpref⟩

/-! ### Lifting the per-segment postcondition to `MemBytesAt (concatSegs segs)`

The outer loop's per-segment postcondition (segment `k`'s bytes at cumulative
offset `psum slen k`) is the flattened-index memory relation `MemBytesAt obase
(concatSegs segs)` — every byte of the concatenation in its slot. The bridge is a
concatenation-index induction. -/

theorem totalLen_append : ∀ (a b : List Seg), totalLen (a ++ b) = totalLen a + totalLen b := by
  intro a b
  induction a with
  | nil => simp [totalLen]
  | cons hd t ih => obtain ⟨sr, bs⟩ := hd; simp only [List.cons_append, totalLen, ih]; omega

/-- The cumulative offset `psum` of the per-segment byte lengths equals the total
byte length of the length-`j` prefix. -/
theorem psum_take (segs : List Seg) : ∀ j,
    psum (fun k => (segs[k]!).2.length) j = totalLen (segs.take j) := by
  intro j
  induction j with
  | zero => simp [psum, totalLen]
  | succ n ih =>
    rw [psum, ih, List.take_add_one, totalLen_append]
    congr 1
    rcases hn : segs[n]? with _ | x
    · have hd : segs[n]! = (default : Seg) := by
        rw [List.getElem!_eq_getElem?_getD, hn]; rfl
      rw [hd]; rfl
    · have hd : segs[n]! = x := by
        rw [List.getElem!_eq_getElem?_getD, hn]; rfl
      rw [hd]; simp [Option.toList, totalLen]

/-- The concatenation-index induction: given each segment's bytes landed at its
running offset (from a base `base0`), every byte of `concatSegs segs` sits in its
output slot. -/
theorem concat_membytes_aux (obase : Word) (s : PancakeState σ) :
    ∀ (segs : List Seg) (base0 : Nat),
    (∀ k m, k < segs.length → m < (segs[k]!).2.length →
       s.memory (obase + BitVec.ofNat 64 (base0 + totalLen (segs.take k) + m))
         = wordOfByte ((segs[k]!).2)[m]!) →
    ∀ i, i < (concatSegs segs).length →
       s.memory (obase + BitVec.ofNat 64 (base0 + i)) = wordOfByte (concatSegs segs)[i]! := by
  intro segs
  induction segs with
  | nil => intro base0 _ i hi; simp [concatSegs] at hi
  | cons hd rest ih =>
    obtain ⟨sr, bs⟩ := hd
    intro base0 hpost i hi
    rw [concatSegs] at hi ⊢
    have h0idx : ((sr, bs) :: rest)[0]! = (sr, bs) := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_cons_zero]; rfl
    have hsuccidx : ∀ k, ((sr, bs) :: rest)[k + 1]! = rest[k]! := by
      intro k; rw [List.getElem!_eq_getElem?_getD, List.getElem?_cons_succ,
                   ← List.getElem!_eq_getElem?_getD]
    by_cases hib : i < bs.length
    · have h0 := hpost 0 i (by simp) (by rw [h0idx]; exact hib)
      rw [bytes_append_left bs _ i hib]
      rw [show base0 + totalLen (((sr, bs) :: rest).take 0) + i = base0 + i from by simp [totalLen]] at h0
      rw [h0idx] at h0
      exact h0
    · have hile : bs.length ≤ i := by omega
      have hi2 : i - bs.length < (concatSegs rest).length := by
        rw [List.length_append] at hi; omega
      have hpost' : ∀ k m, k < rest.length → m < (rest[k]!).2.length →
          s.memory (obase + BitVec.ofNat 64 ((base0 + bs.length) + totalLen (rest.take k) + m))
            = wordOfByte ((rest[k]!).2)[m]! := by
        intro k m hk hm
        have hk' : k + 1 < ((sr, bs) :: rest).length := by simp only [List.length_cons]; omega
        have hm' : m < (((sr, bs) :: rest)[k + 1]!).2.length := by rw [hsuccidx]; exact hm
        have hh := hpost (k + 1) m hk' hm'
        rw [show ((sr, bs) :: rest).take (k + 1) = (sr, bs) :: rest.take k from rfl, totalLen,
            hsuccidx,
            show base0 + (bs.length + totalLen (rest.take k)) + m
              = base0 + bs.length + totalLen (rest.take k) + m from by omega] at hh
        exact hh
      have hrec := ih (base0 + bs.length) hpost' (i - bs.length) hi2
      rw [bytes_append_right bs _ i hile,
          show base0 + i = base0 + bs.length + (i - bs.length) from by omega]
      exact hrec

/-- **THE FLATTENED MEMORY RELATION.** The per-segment postcondition (segment `k`'s
bytes at cumulative offset `psum slen k`) IS `MemBytesAt obase (concatSegs segs)`:
every byte of the concatenation in its output slot. -/
theorem concat_membytes (segs : List Seg) (obase : Word) (s : PancakeState σ)
    (hpost : ∀ k m, k < segs.length → m < (segs[k]!).2.length →
       s.memory (obase + BitVec.ofNat 64 (psum (fun k => (segs[k]!).2.length) k + m))
         = wordOfByte ((segs[k]!).2)[m]!) :
    MemBytesAt s obase (concatSegs segs) := by
  intro i hi
  have hpost' : ∀ k m, k < segs.length → m < (segs[k]!).2.length →
      s.memory (obase + BitVec.ofNat 64 (0 + totalLen (segs.take k) + m))
        = wordOfByte ((segs[k]!).2)[m]! := by
    intro k m hk hm; have := hpost k m hk hm; rw [psum_take] at this; simpa using this
  have := concat_membytes_aux obase s segs 0 hpost' i hi
  simpa using this

/-- **THE OUTER LOOP LANDS `concatSegs segs`.** For a segment (header) list held in
memory — record `k` at `recPtr k` giving its source base and byte length, its bytes
at that base — the outer `segWhile` runs to completion and lands the output region
at `obase` byte-for-byte equal to `concatSegs segs` (`MemBytesAt`), via the real
outer loop over the list and per-segment inner copy. -/
theorem segWhile_membytes (o : Oracle σ) (segs : List Seg) (recPtr : Nat → Word) (obase : Word)
    (hN63 : totalLen segs < 2 ^ 63) (hcount63 : segs.length < 2 ^ 63)
    (hfit : ∀ k, k < segs.length →
        psum (fun k => (segs[k]!).2.length) k + (segs[k]!).2.length ≤ totalLen segs)
    (hOinj : ∀ p q, p < totalLen segs → q < totalLen segs →
        obase + BitVec.ofNat 64 p = obase + BitVec.ofNat 64 q → p = q)
    (hOS : ∀ k m q, k < segs.length → m < (segs[k]!).2.length → q < totalLen segs →
        (segs[k]!).1 + BitVec.ofNat 64 m ≠ obase + BitVec.ofNat 64 q)
    (hOR : ∀ k q, k < segs.length → q < totalLen segs →
        recPtr k ≠ obase + BitVec.ofNat 64 q ∧ recPtr k + w8 ≠ obase + BitVec.ofNat 64 q)
    (hstep : ∀ k, recPtr (k + 1) = recPtr k + w32)
    (s : PancakeState σ)
    (hj : s.locals "j" = some (BitVec.ofNat 64 0))
    (hcount : s.locals "count" = some (BitVec.ofNat 64 segs.length))
    (hoff : s.locals "off" = some (BitVec.ofNat 64 0))
    (hp : s.locals "p" = some (recPtr 0))
    (hobase : s.locals "obase" = some obase)
    (hrec : ∀ k, k < segs.length →
        s.memaddrs (recPtr k) = true ∧ s.memory (recPtr k) = (segs[k]!).1 ∧
        s.memaddrs (recPtr k + w8) = true ∧
        s.memory (recPtr k + w8) = BitVec.ofNat 64 (segs[k]!).2.length)
    (hsrc : ∀ k m, k < segs.length → m < (segs[k]!).2.length →
        s.memaddrs ((segs[k]!).1 + BitVec.ofNat 64 m) = true ∧
        s.memory ((segs[k]!).1 + BitVec.ofNat 64 m) = wordOfByte ((segs[k]!).2)[m]!)
    (hOaddr : ∀ q, q < totalLen segs → s.memaddrs (obase + BitVec.ofNat 64 q) = true)
    (hclock : segs.length + totalLen segs ≤ s.clock) :
    ∃ s', PancakeSem o segWhile s = (none, s') ∧ MemBytesAt s' obase (concatSegs segs) := by
  obtain ⟨s', hs'eq, hpost⟩ :=
    segWhile_writes o segs.length recPtr (fun k => (segs[k]!).1) (fun k => (segs[k]!).2.length)
      (fun k m => wordOfByte ((segs[k]!).2)[m]!) obase (totalLen segs)
      hcount63 hN63 hfit hOinj hOS hOR hstep s hj hcount hoff hp hobase hrec hsrc hOaddr hclock
  exact ⟨s', hs'eq, concat_membytes segs obase s' hpost⟩

/-! ## 4. The loop's segments ARE the response's headers

Each header renders to the segment `name ": " value CRLF` (`segOf`); the
concatenation of those per-header segments (plus the closing blank line) is exactly
the header block segment of the wire framing (`headerSeg`, from SerializeFull). So
the segments the outer loop writes are precisely the response's headers, and they
appear byte-for-byte in `serialize resp`. -/

/-- One header rendered as its output segment: `name ": " value` + CRLF. -/
def segOf (h : Bytes × Bytes) : Bytes := headerLine h ++ crlf

/-- The CRLF-joined header block, plus one trailing CRLF, is the FLATTENING of the
per-header segments — i.e. exactly one `name ": " value CRLF` segment per header. -/
theorem renderHeaders_flatten : ∀ (hs : List (Bytes × Bytes)), hs ≠ [] →
    renderHeaders hs ++ crlf = (hs.map segOf).flatten := by
  intro hs
  induction hs with
  | nil => intro h; exact absurd rfl h
  | cons a t ih =>
    intro _
    cases t with
    | nil => show renderHeaders [a] ++ crlf = _; simp [renderHeaders, segOf]
    | cons b t' =>
      have hIH : renderHeaders (b :: t') ++ crlf = ((b :: t').map segOf).flatten := ih (by simp)
      show (headerLine a ++ crlf ++ renderHeaders (b :: t')) ++ crlf = ((a :: b :: t').map segOf).flatten
      rw [List.map_cons, List.flatten_cons, ← hIH, segOf]
      simp [List.append_assoc]

/-- **THE HEADER BLOCK IS THE FLATTENED PER-HEADER SEGMENTS.** The header segment
of the wire framing (`headerSeg = headerBlock ++ CRLF ++ CRLF`) equals the
concatenation of every header's `name ": " value CRLF` segment, plus the closing
CRLF — so the outer loop over the header list writes precisely the response's
headers into the serialized bytes. -/
theorem header_seg_framing (resp : Response) :
    headerSeg resp = ((allHeaders (build resp)).map segOf).flatten ++ crlf := by
  have hne : allHeaders (build resp) ≠ [] := by simp [allHeaders]
  show headerBlockOf resp ++ crlf ++ crlf = _
  rw [headerBlockOf, renderHeaders_flatten (allHeaders (build resp)) hne]

/-! ### Non-vacuity on the real `sampleResp` (a `200 OK`, one caller header) -/

-- the two per-header segments are the real header lines "X-A: 1\r\n" and
-- "Content-Length: 2\r\n" (the derived length header included):
#guard (allHeaders (build sampleResp)).map segOf
       = [[88, 45, 65, 58, 32, 49, 13, 10],
          [67, 111, 110, 116, 101, 110, 116, 45, 76, 101, 110, 103, 116, 104, 58, 32, 50, 13, 10]]
-- their flattening + CRLF is exactly the header segment (29 bytes):
#guard ((allHeaders (build sampleResp)).map segOf).flatten ++ crlf = headerSeg sampleResp
#guard (((allHeaders (build sampleResp)).map segOf).flatten ++ crlf).length = 29
-- two segments, genuinely distinct (a real multi-header split):
#guard ((allHeaders (build sampleResp)).map segOf).length = 2

/-! ## 5. Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}, 0 sorryAx. -/

#print axioms copyWhile_locals
#print axioms segStep
#print axioms segLoop
#print axioms segWhile_writes
#print axioms concat_membytes
#print axioms segWhile_membytes
#print axioms header_seg_framing

end Pancake.SerializeHeaders
