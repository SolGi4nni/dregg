/-
  Pancake/NatToDecFull.lean — the MULTI-DIGIT `natToDec` render as a REAL Pancake
  program: the outer digit loop over NatToDecCompile's divide-by-10 keystone.
  This closes the residual NatToDecCompile.lean names ("the multi-digit OUTER
  `While` that nests `divWhile` and lays the whole `natToDec n` byte string into
  a descending memory buffer is NOT yet closed here").

  GROUND (re-checked against ~/src/cakeml @ `ed31510b3`, 2026-07-17). The pinned
  CakeML Pancake has NO divide/modulo anywhere in its expression language:
    * panLangScript.sml:42   `panop = (* Div | *)Mul (* | Mod*)`   (COMMENTED OUT)
    * panSemScript.sml:191   `pan_op Mul [w1:'a word;w2] = SOME(w1 * w2) ∧
                              pan_op _ _ = NONE`
    * asmScript.sml:79       `binop = Add | Sub | And | Or | Xor`  (no Div)
  So extending `PancakeExp` with a Div/Mod constructor would model an operator
  the targeted compiler chain CANNOT emit — a fabricated semantics. The faithful
  divide-by-10 is NatToDecCompile's `divWhile` (repeated subtraction, only
  `Op Sub` / `Op Add` / `Cmp NotLess`), already proven (`divWhile_sem`).

  THIS FILE builds the digit loop around it, all inside the modelled subset:

      natToDecProg =                          -- do-while: ≥ 1 digit, so 0 ↦ "0"
        digitBody ;
        while (n) { digitBody }

      digitBody =                             -- peel ONE decimal digit
        q := 0;
        while (10 <= n) { n := n - 10; q := q + 1 }   -- divWhile: n%10, n/10
        p := p - 1;
        strb p, n + 48;                       -- StoreByte: ASCII digit, desc.
        n := q

  and proves `natToDecProg_sem`: from `n = m` (`m < 2^63`), end-pointer `p0`,
  enough clock, the run terminates normally and the memory at
  `[p0 - L, p0)` (`L = (natToDec m).length`) holds EXACTLY the bytes of
  `natToDec m` (most-significant first — the descending store reverses the
  low-digit-first peel), every other byte and every other state field framed.
  `natToDec` is the PROVEN render spec (`natToDec_readback` reads the digits
  back as `m`; the SerializeCompile `#guard` corpus pins it byte-identical to
  `Nat.repr` on 200/404/48/0).

  (⊆ {propext, Classical.choice, Quot.sound}). Stack L (Lean model of Pancake);
  no machine-code claim. Non-vacuity: the postcondition pins every rendered byte
  to `(natToDec m)[j]` and the pointer to `p0 - L`; the corpus examples
  instantiate it on 404 / 0 with the literal bytes 52/48/52 and 48.
-/
import Pancake.NatToDecCompile
import Pancake.BytesModel

namespace Pancake.NatToDecFull

open Pancake Pancake.EmitCorrect Pancake.EmitCorrectLoop Pancake.SerializeCompile
open Pancake.NatToDecCompile Pancake.BytesModel

variable {σ : Type}

/-! ## 0. Word-address algebra (64-bit, no wrap side-conditions needed for
subtraction cancellation) -/

theorem ofNat64_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : BitVec.ofNat 64 a = BitVec.ofNat 64 b) : a = b := by
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at h'
  omega

theorem ofNat64_ne_zero {m : Nat} (h0 : m ≠ 0) (hlt : m < 2 ^ 64) :
    BitVec.ofNat 64 m ≠ (0 : Word) := by
  intro h
  have h' := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, show ((0 : Word)).toNat = 0 from rfl] at h'
  omega

/-- The descending address walk, one step: `p - (j+1) = (p - 1) - j`. -/
theorem sub_ofNat_succ (p : Word) (j : Nat) :
    p - BitVec.ofNat 64 (j + 1) = (p - BitVec.ofNat 64 1) - BitVec.ofNat 64 j := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- Left-cancellation for word subtraction (exact — no non-wrap condition). -/
theorem sub_left_cancel {p x y : Word} (h : p - x = p - y) : x = y := by
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_sub] at h'
  have hx := x.isLt
  have hy := y.isLt
  have hp := p.isLt
  apply BitVec.eq_of_toNat_eq
  omega

/-! ## 1. `decAux`/`natToDec` structural lemmas (the spec side of the loop) -/

/-- `decAux` ignores surplus fuel. -/
theorem decAux_fuel_irrel :
    ∀ (f g n : Nat) (acc : Bytes), n < f → n < g → decAux f n acc = decAux g n acc := by
  intro f
  induction f with
  | zero => intro g n acc hf _; omega
  | succ f ih =>
    intro g n acc hf hg
    cases g with
    | zero => omega
    | succ g =>
      by_cases hn : n < 10
      · have h1 : decAux (f + 1) n acc = digitByte n :: acc := if_pos hn
        have h2 : decAux (g + 1) n acc = digitByte n :: acc := if_pos hn
        rw [h1, h2]
      · have h1 : decAux (f + 1) n acc = decAux f (n / 10) (digitByte (n % 10) :: acc) :=
          if_neg hn
        have h2 : decAux (g + 1) n acc = decAux g (n / 10) (digitByte (n % 10) :: acc) :=
          if_neg hn
        have hd : n / 10 < n := Nat.div_lt_self (by omega) (by omega)
        rw [h1, h2]
        exact ih g (n / 10) _ (by omega) (by omega)

/-- The accumulator is an append: `decAux f n acc = decAux f n [] ++ acc`. -/
theorem decAux_append :
    ∀ (f n : Nat) (acc : Bytes), n < f → decAux f n acc = decAux f n [] ++ acc := by
  intro f
  induction f with
  | zero => intro n acc h; omega
  | succ f ih =>
    intro n acc h
    by_cases hn : n < 10
    · have h1 : decAux (f + 1) n acc = digitByte n :: acc := if_pos hn
      have h2 : decAux (f + 1) n ([] : Bytes) = digitByte n :: [] := if_pos hn
      rw [h1, h2]
      rfl
    · have h1 : decAux (f + 1) n acc = decAux f (n / 10) (digitByte (n % 10) :: acc) :=
        if_neg hn
      have h2 : decAux (f + 1) n ([] : Bytes)
          = decAux f (n / 10) (digitByte (n % 10) :: []) := if_neg hn
      have hd : n / 10 < n := Nat.div_lt_self (by omega) (by omega)
      have hdf : n / 10 < f := by omega
      rw [h1, h2, ih (n / 10) _ hdf, ih (n / 10) (digitByte (n % 10) :: []) hdf,
          List.append_assoc]
      rfl

/-- One digit: `natToDec m = [digitByte m]` for `m < 10`. -/
theorem natToDec_lt10 {m : Nat} (hm : m < 10) : natToDec m = [digitByte m] := by
  show decAux (m + 1) m [] = [digitByte m]
  exact if_pos hm

/-- The peel: for `m ≥ 10` the render is the quotient's render with the low
digit appended — EXACTLY what one `digitBody` + recursion realises. -/
theorem natToDec_split {m : Nat} (hm : 10 ≤ m) :
    natToDec m = natToDec (m / 10) ++ [digitByte (m % 10)] := by
  have hdiv : m / 10 < m := Nat.div_lt_self (by omega) (by omega)
  have h1 : natToDec m = decAux m (m / 10) (digitByte (m % 10) :: []) := if_neg (by omega)
  rw [h1, decAux_append m (m / 10) _ hdiv,
      decAux_fuel_irrel m (m / 10 + 1) (m / 10) [] hdiv (by omega)]
  rfl

theorem natToDec_length_pos (m : Nat) : 0 < (natToDec m).length := by
  by_cases hm : m < 10
  · rw [natToDec_lt10 hm]; simp
  · rw [natToDec_split (by omega)]; simp

theorem natToDec_length_le (m : Nat) : (natToDec m).length ≤ m + 1 := by
  by_cases hm : m < 10
  · rw [natToDec_lt10 hm]; simp
  · rw [natToDec_split (by omega)]
    have ih := natToDec_length_le (m / 10)
    have hd : m / 10 < m := Nat.div_lt_self (by omega) (by omega)
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
termination_by m
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-! ## 2. Control-flow helpers over `PancakeSem` -/

/-- `set_var` reads back what it wrote. -/
theorem setLocal_same (lc : String → Option Value) (v : String) (val : Value) :
    setLocal lc v val v = some val := by
  simp [setLocal]

/-- `set_var` leaves other variables alone. -/
theorem setLocal_ne (lc : String → Option Value) (v : String) (val : Value)
    {k : String} (h : k ≠ v) : setLocal lc v val k = lc k := by
  simp [setLocal, h]

/-- `Seq` step with a non-increasing clock: the inlined `fix_clock` clamp
collapses (`min s.clock s1.clock = s1.clock`). -/
theorem seq_step (o : Oracle σ) {c1 c2 : PancakeProg} {s s1 : PancakeState σ}
    (h : PancakeSem o c1 s = (none, s1)) (hclk : s1.clock ≤ s.clock) :
    PancakeSem o (.seq c1 c2) s = PancakeSem o c2 s1 := by
  rw [sem_seq_none (oracle := o) h]
  have hm : min s.clock s1.clock = s1.clock := by omega
  rw [hm]

/-- One `While` iteration for ANY true guard word and a body consuming any
number of ticks (generalises `NatToDecCompile.while_iter`, which is
exact-one-tick): guard `w ≠ 0`, body runs on `dec_clock` to `(NONE, sb)`,
`fix_clock` collapses since `sb.clock ≤ s.clock - 1`. -/
theorem while_iter_le (o : Oracle σ) {e : PancakeExp} {c : PancakeProg}
    {s sb : PancakeState σ} {w : Word}
    (hg : eval s e = some w) (hw : w ≠ 0) (hclk : s.clock ≠ 0)
    (hbody : PancakeSem o c (decClock s) = (none, sb))
    (hsbclk : sb.clock ≤ s.clock - 1) :
    PancakeSem o (.while_ e c) s = PancakeSem o (.while_ e c) sb := by
  have hcollapse : ({ sb with clock := min (s.clock - 1) sb.clock } : PancakeState σ) = sb := by
    have hm : min (s.clock - 1) sb.clock = sb.clock := by omega
    rw [hm]
  rw [PancakeSem]
  simp only [hg, ne_eq, eq_false hw, not_false_eq_true, if_true, hclk, if_false,
             clampClock, hbody, hcollapse]

/-! ## 3. `digitBody` — peel ONE decimal digit (divide-by-10 by subtraction +
the descending `StoreByte`) -/

/-- One digit peeled, all inside the modelled/emittable subset:
`q := 0; divWhile; p := p - 1; strb p, n + 48; n := q`. -/
def digitBody : PancakeProg :=
  .seq (.assign "q" (.const 0))
  (.seq divWhile
  (.seq (.assign "p" (.op .sub (.var "p") (.const (BitVec.ofNat 64 1))))
  (.seq (.storeByte (.var "p") (.op .add (.var "n") (.const (BitVec.ofNat 64 48))))
        (.assign "n" (.var "q")))))

/-- `digitBody` executed: from `n = m`, `p = p0`, it consumes `m / 10` clock
(the inner subtraction loop), stores `digitByte (m % 10)` at `p0 - 1`
(`putByte`, the panSem `mem_store_byte` image), decrements `p`, and leaves
`n = q = m / 10`. Everything else framed. -/
theorem digitBody_sem (o : Oracle σ) {m : Nat} {p0 : Word} {s : PancakeState σ}
    (hn : s.locals "n" = some (BitVec.ofNat 64 m))
    (hp : s.locals "p" = some p0)
    (hm63 : m < 2 ^ 63)
    (hdm : s.memaddrs (byteAlign (p0 - BitVec.ofNat 64 1)) = true)
    (hclk : m / 10 ≤ s.clock) :
    ∃ s', PancakeSem o digitBody s = (none, s') ∧
      s'.locals "n" = some (BitVec.ofNat 64 (m / 10)) ∧
      s'.locals "q" = some (BitVec.ofNat 64 (m / 10)) ∧
      s'.locals "p" = some (p0 - BitVec.ofNat 64 1) ∧
      s'.clock = s.clock - m / 10 ∧
      s'.memory = putByte s.memory s.be (p0 - BitVec.ofNat 64 1) (digitByte (m % 10)) ∧
      s'.memaddrs = s.memaddrs ∧ s'.be = s.be ∧ s'.baseAddr = s.baseAddr ∧
      (∀ key, key ≠ "n" → key ≠ "q" → key ≠ "p" → s'.locals key = s.locals key) := by
  -- step 1: q := 0
  have hA : PancakeSem o (.assign "q" (.const 0)) s
      = (none, { s with locals := setLocal s.locals "q" (0 : Word) }) :=
    sem_assign (oracle := o) rfl
  -- step 2: divWhile from the q-cleared state
  obtain ⟨s2, hW, hn2, hq2, hclk2, hmem2, hma2, hbe2, hba2, hfr2⟩ :=
    divWhile_sem o (m / 10) m 0 { s with locals := setLocal s.locals "q" (0 : Word) }
      (by show setLocal s.locals "q" (0 : Word) "n" = _
          rw [setLocal_ne _ _ _ (by decide)]
          exact hn)
      (by show setLocal s.locals "q" (0 : Word) "q" = _
          rw [setLocal_same])
      hm63 rfl hclk
  -- normalise the s2 field facts to `s`-forms (record-literal projections are defeq)
  replace hclk2 : s2.clock = s.clock - m / 10 := hclk2
  replace hmem2 : s2.memory = s.memory := hmem2
  replace hma2 : s2.memaddrs = s.memaddrs := hma2
  replace hbe2 : s2.be = s.be := hbe2
  replace hba2 : s2.baseAddr = s.baseAddr := hba2
  have hfr2' : ∀ key, key ≠ "n" → key ≠ "q" → s2.locals key = s.locals key := by
    intro key hkn hkq
    rw [hfr2 key hkn hkq]
    show setLocal s.locals "q" (0 : Word) key = s.locals key
    rw [setLocal_ne _ _ _ hkq]
  have hq2' : s2.locals "q" = some (BitVec.ofNat 64 (m / 10)) := by
    rw [hq2]
    congr 1
    exact BitVec.zero_add _
  -- step 3: p := p - 1
  have hp2 : s2.locals "p" = some p0 := by
    rw [hfr2' "p" (by decide) (by decide)]
    exact hp
  have hP : PancakeSem o (.assign "p" (.op .sub (.var "p") (.const (BitVec.ofNat 64 1)))) s2
      = (none, { s2 with locals := setLocal s2.locals "p" (p0 - BitVec.ofNat 64 1) }) :=
    sem_assign (oracle := o) (by simp only [eval, hp2])
  -- step 4: strb p, n + 48  (digit_store, the panSem byte store)
  have hstore : memStoreByte s2.memory s2.memaddrs s2.be (p0 - BitVec.ofNat 64 1)
      (digitByte (m % 10))
      = some (putByte s.memory s.be (p0 - BitVec.ofNat 64 1) (digitByte (m % 10))) := by
    rw [hmem2, hma2, hbe2]
    exact memStore_eq s.memory s.memaddrs s.be _ _ hdm
  have hS : PancakeSem o
      (.storeByte (.var "p") (.op .add (.var "n") (.const (BitVec.ofNat 64 48))))
      { s2 with locals := setLocal s2.locals "p" (p0 - BitVec.ofNat 64 1) }
      = (none, { s2 with
          locals := setLocal s2.locals "p" (p0 - BitVec.ofNat 64 1),
          memory := putByte s.memory s.be (p0 - BitVec.ofNat 64 1) (digitByte (m % 10)) }) := by
    apply digit_store o (d := m % 10)
    · show setLocal s2.locals "p" (p0 - BitVec.ofNat 64 1) "n" = _
      rw [setLocal_ne _ _ _ (by decide)]
      exact hn2
    · show setLocal s2.locals "p" (p0 - BitVec.ofNat 64 1) "p" = _
      rw [setLocal_same]
    · exact hstore
  -- step 5: n := q
  have hq4 : ({ s2 with
      locals := setLocal s2.locals "p" (p0 - BitVec.ofNat 64 1),
      memory := putByte s.memory s.be (p0 - BitVec.ofNat 64 1) (digitByte (m % 10)) }
        : PancakeState σ).locals "q" = some (BitVec.ofNat 64 (m / 10)) := by
    show setLocal s2.locals "p" (p0 - BitVec.ofNat 64 1) "q" = _
    rw [setLocal_ne _ _ _ (by decide)]
    exact hq2'
  have hN : PancakeSem o (.assign "n" (.var "q"))
      { s2 with
        locals := setLocal s2.locals "p" (p0 - BitVec.ofNat 64 1),
        memory := putByte s.memory s.be (p0 - BitVec.ofNat 64 1) (digitByte (m % 10)) }
      = (none, { s2 with
          locals := setLocal (setLocal s2.locals "p" (p0 - BitVec.ofNat 64 1)) "n"
            (BitVec.ofNat 64 (m / 10)),
          memory := putByte s.memory s.be (p0 - BitVec.ofNat 64 1) (digitByte (m % 10)) }) :=
    sem_assign (oracle := o) hq4
  -- assemble the run
  refine ⟨{ s2 with
      locals := setLocal (setLocal s2.locals "p" (p0 - BitVec.ofNat 64 1)) "n"
        (BitVec.ofNat 64 (m / 10)),
      memory := putByte s.memory s.be (p0 - BitVec.ofNat 64 1) (digitByte (m % 10)) },
    ?_, ?_, ?_, ?_, hclk2, rfl, hma2, hbe2, hba2, ?_⟩
  · unfold digitBody
    rw [seq_step o hA (Nat.le_refl _),
        seq_step o hW (by show s2.clock ≤ s.clock; omega),
        seq_step o hP (Nat.le_refl _),
        seq_step o hS (Nat.le_refl _)]
    exact hN
  · show setLocal (setLocal s2.locals "p" (p0 - BitVec.ofNat 64 1)) "n"
        (BitVec.ofNat 64 (m / 10)) "n" = _
    rw [setLocal_same]
  · show setLocal (setLocal s2.locals "p" (p0 - BitVec.ofNat 64 1)) "n"
        (BitVec.ofNat 64 (m / 10)) "q" = _
    rw [setLocal_ne _ _ _ (by decide), setLocal_ne _ _ _ (by decide)]
    exact hq2'
  · show setLocal (setLocal s2.locals "p" (p0 - BitVec.ofNat 64 1)) "n"
        (BitVec.ofNat 64 (m / 10)) "p" = _
    rw [setLocal_ne _ _ _ (by decide), setLocal_same]
  · intro key h1 h2 h3
    show setLocal (setLocal s2.locals "p" (p0 - BitVec.ofNat 64 1)) "n"
        (BitVec.ofNat 64 (m / 10)) key = s.locals key
    rw [setLocal_ne _ _ _ h1, setLocal_ne _ _ _ h3]
    exact hfr2' key h1 h2

/-! ## 4. The digit-render postcondition -/

/-- Postcondition of rendering `m`'s decimal digits with end-pointer `p0`:
`n = 0`, `p = p0 - L`, the `L = (natToDec m).length` ASCII digit bytes laid at
`[p0 - L, p0)` most-significant first, every OTHER byte (read through
`mem_load_byte`) and every other state field / local framed. -/
abbrev RenderPost (m : Nat) (p0 : Word) (s0 s' : PancakeState σ) : Prop :=
  s'.locals "n" = some (0 : Word) ∧
  s'.locals "p" = some (p0 - BitVec.ofNat 64 (natToDec m).length) ∧
  (∀ j b, (natToDec m)[j]? = some b →
    memLoadByte s'.memory s'.memaddrs s'.be
      (p0 - BitVec.ofNat 64 ((natToDec m).length - j)) = some b) ∧
  (∀ a, (∀ j, j < (natToDec m).length → a ≠ p0 - BitVec.ofNat 64 (j + 1)) →
    memLoadByte s'.memory s'.memaddrs s'.be a
      = memLoadByte s0.memory s0.memaddrs s0.be a) ∧
  s'.memaddrs = s0.memaddrs ∧ s'.be = s0.be ∧ s'.baseAddr = s0.baseAddr ∧
  (∀ key, key ≠ "n" → key ≠ "q" → key ≠ "p" → s'.locals key = s0.locals key)

/-- The `m < 10` case: ONE `digitBody` (already run, post-state `sb`) IS the
whole render. -/
theorem single_digit_post {m : Nat} {p0 : Word} {s0 sb : PancakeState σ}
    (hm10 : m < 10)
    (hsbn : sb.locals "n" = some (BitVec.ofNat 64 (m / 10)))
    (hsbp : sb.locals "p" = some (p0 - BitVec.ofNat 64 1))
    (hsbmem : sb.memory = putByte s0.memory s0.be (p0 - BitVec.ofNat 64 1)
      (digitByte (m % 10)))
    (hsbma : sb.memaddrs = s0.memaddrs) (hsbbe : sb.be = s0.be)
    (hsbba : sb.baseAddr = s0.baseAddr)
    (hsbfr : ∀ key, key ≠ "n" → key ≠ "q" → key ≠ "p" → sb.locals key = s0.locals key)
    (hdm1 : s0.memaddrs (byteAlign (p0 - BitVec.ofNat 64 1)) = true) :
    RenderPost m p0 s0 sb := by
  have hL : natToDec m = [digitByte m] := natToDec_lt10 hm10
  have hLen : (natToDec m).length = 1 := by rw [hL]; rfl
  have hmod : m % 10 = m := Nat.mod_eq_of_lt hm10
  refine ⟨?_, ?_, ?_, ?_, hsbma, hsbbe, hsbba, hsbfr⟩
  · rw [hsbn, Nat.div_eq_of_lt hm10]
    rfl
  · rw [hLen]
    exact hsbp
  · intro j b hjb
    rw [hL] at hjb
    cases j with
    | zero =>
      have hb : b = digitByte m := by
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hjb
        exact hjb.symm
      rw [hLen, hb, hsbmem, hsbma, hsbbe, hmod]
      exact load_putByte_same s0.memory s0.memaddrs s0.be _ _ hdm1
    | succ j =>
      simp at hjb
  · intro a ha
    have ha0 : a ≠ p0 - BitVec.ofNat 64 1 := ha 0 (by rw [hLen]; omega)
    rw [hsbmem, hsbma, hsbbe]
    exact load_putByte_diff s0.memory s0.memaddrs s0.be _ _ a ha0

/-- The `m ≥ 10` composition: one `digitBody` peeled the low digit into
`p0 - 1` (post-state `sb`), and the recursive render of `m / 10` from `sb`
with end-pointer `p0 - 1` reached `s'`. Together they render `m`. The peeled
byte at `p0 - 1` SURVIVES the recursive run because the recursion writes only
strictly below it (its frame clause + subtraction cancellation). -/
theorem multi_digit_post {m : Nat} {p0 : Word} {s0 sb s' : PancakeState σ}
    (hm10 : 10 ≤ m) (hm63 : m < 2 ^ 63)
    (hsbmem : sb.memory = putByte s0.memory s0.be (p0 - BitVec.ofNat 64 1)
      (digitByte (m % 10)))
    (hsbma : sb.memaddrs = s0.memaddrs) (hsbbe : sb.be = s0.be)
    (hsbba : sb.baseAddr = s0.baseAddr)
    (hsbfr : ∀ key, key ≠ "n" → key ≠ "q" → key ≠ "p" → sb.locals key = s0.locals key)
    (hdm1 : s0.memaddrs (byteAlign (p0 - BitVec.ofNat 64 1)) = true)
    (hpost : RenderPost (m / 10) (p0 - BitVec.ofNat 64 1) sb s') :
    RenderPost m p0 s0 s' := by
  obtain ⟨hn', hp', hbytes, hfr, hma', hbe', hba', hlfr⟩ := hpost
  have hsplit : natToDec m = natToDec (m / 10) ++ [digitByte (m % 10)] :=
    natToDec_split hm10
  have hL'le : (natToDec (m / 10)).length ≤ m / 10 + 1 := natToDec_length_le _
  have hLm : (natToDec m).length = (natToDec (m / 10)).length + 1 := by
    rw [hsplit]
    simp
  refine ⟨hn', ?_, ?_, ?_, hma'.trans hsbma, hbe'.trans hsbbe, hba'.trans hsbba,
          fun key h1 h2 h3 => (hlfr key h1 h2 h3).trans (hsbfr key h1 h2 h3)⟩
  · rw [hLm, sub_ofNat_succ]
    exact hp'
  · -- the byte clause
    intro j b hjb
    rw [hsplit] at hjb
    by_cases hjL : j < (natToDec (m / 10)).length
    · -- an upper digit: rendered by the recursion, one address-step down
      have hjb' : (natToDec (m / 10))[j]? = some b := by
        rw [List.getElem?_append_left hjL] at hjb
        exact hjb
      have haddr : p0 - BitVec.ofNat 64 ((natToDec m).length - j)
          = (p0 - BitVec.ofNat 64 1) - BitVec.ofNat 64 ((natToDec (m / 10)).length - j) := by
        rw [hLm, show (natToDec (m / 10)).length + 1 - j
              = ((natToDec (m / 10)).length - j) + 1 from by omega,
            sub_ofNat_succ]
      rw [haddr]
      exact hbytes j b hjb'
    · -- the low digit at `p0 - 1`: stored by `digitBody`, framed by the recursion
      have hjlt : j < (natToDec (m / 10)).length + 1 := by
        refine (Nat.lt_or_ge j ((natToDec (m / 10)).length + 1)).elim (fun h => h)
          (fun hge => ?_)
        have hnone : (natToDec (m / 10) ++ [digitByte (m % 10)])[j]? = none := by
          apply List.getElem?_eq_none
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        rw [hnone] at hjb
        exact absurd hjb (by simp)
      have hjeq : j = (natToDec (m / 10)).length := by omega
      subst hjeq
      have hb : b = digitByte (m % 10) := by
        rw [List.getElem?_append_right (Nat.le_refl _)] at hjb
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hjb
        exact hjb.symm
      have haddr : (natToDec m).length - (natToDec (m / 10)).length = 1 := by
        rw [hLm]
        omega
      rw [haddr, hb]
      have hane : ∀ j', j' < (natToDec (m / 10)).length →
          p0 - BitVec.ofNat 64 1 ≠ (p0 - BitVec.ofNat 64 1) - BitVec.ofNat 64 (j' + 1) := by
        intro j' hj' heq
        rw [← sub_ofNat_succ] at heq
        have h1 : (1 : Nat) = j' + 1 + 1 :=
          ofNat64_inj (by omega) (by omega) (sub_left_cancel heq)
        omega
      rw [hfr _ hane, hsbmem, hsbma, hsbbe]
      exact load_putByte_same s0.memory s0.memaddrs s0.be _ _ hdm1
  · -- the frame clause
    intro a ha
    have ha0 : a ≠ p0 - BitVec.ofNat 64 1 := ha 0 (by rw [hLm]; omega)
    have ha' : ∀ j', j' < (natToDec (m / 10)).length →
        a ≠ (p0 - BitVec.ofNat 64 1) - BitVec.ofNat 64 (j' + 1) := by
      intro j' hj'
      rw [← sub_ofNat_succ]
      exact ha (j' + 1) (by rw [hLm]; omega)
    rw [hfr a ha', hsbmem, hsbma, hsbbe]
    exact load_putByte_diff s0.memory s0.memaddrs s0.be _ _ a ha0

/-! ## 5. The digit loop -/

/-- Structural fuel core for the clock budget (`m ≤ f` bounds the recursion). -/
def digitFuelAux : Nat → Nat → Nat
  | 0, _ => 1
  | f + 1, m => if m < 10 then 1 else 1 + m / 10 + digitFuelAux f (m / 10)

/-- Exact clock budget of the digit WHILE-loop from `n = m ≠ 0`: one guard tick
plus `m/10` subtraction ticks per digit position. -/
def digitFuel (m : Nat) : Nat := digitFuelAux m m

theorem digitFuelAux_irrel :
    ∀ (f g m : Nat), m ≤ f → m ≤ g → digitFuelAux f m = digitFuelAux g m := by
  intro f
  induction f with
  | zero =>
    intro g m hf _
    have hm : m = 0 := by omega
    subst hm
    cases g with
    | zero => rfl
    | succ g =>
      have h2 : digitFuelAux (g + 1) 0 = 1 := if_pos (by omega)
      rw [h2]
      rfl
  | succ f ih =>
    intro g m hf hg
    cases g with
    | zero =>
      have hm : m = 0 := by omega
      subst hm
      have h1 : digitFuelAux (f + 1) 0 = 1 := if_pos (by omega)
      rw [h1]
      rfl
    | succ g =>
      by_cases hm : m < 10
      · have h1 : digitFuelAux (f + 1) m = 1 := if_pos hm
        have h2 : digitFuelAux (g + 1) m = 1 := if_pos hm
        rw [h1, h2]
      · have h1 : digitFuelAux (f + 1) m = 1 + m / 10 + digitFuelAux f (m / 10) :=
          if_neg hm
        have h2 : digitFuelAux (g + 1) m = 1 + m / 10 + digitFuelAux g (m / 10) :=
          if_neg hm
        have hd : m / 10 < m := Nat.div_lt_self (by omega) (by omega)
        rw [h1, h2, ih g (m / 10) (by omega) (by omega)]

theorem digitFuel_lt10 {m : Nat} (h : m < 10) : digitFuel m = 1 := by
  cases m with
  | zero => rfl
  | succ k =>
    show digitFuelAux (k + 1) (k + 1) = 1
    exact if_pos h

theorem digitFuel_ge10 {m : Nat} (h : ¬ m < 10) :
    digitFuel m = 1 + m / 10 + digitFuel (m / 10) := by
  cases m with
  | zero => omega
  | succ k =>
    show digitFuelAux (k + 1) (k + 1) = 1 + (k + 1) / 10 + digitFuel ((k + 1) / 10)
    have h1 : digitFuelAux (k + 1) (k + 1)
        = 1 + (k + 1) / 10 + digitFuelAux k ((k + 1) / 10) := if_neg h
    have hd : (k + 1) / 10 < k + 1 := Nat.div_lt_self (by omega) (by omega)
    rw [h1, digitFuelAux_irrel k ((k + 1) / 10) ((k + 1) / 10) (by omega) (Nat.le_refl _)]
    rfl

theorem digitFuel_pos (m : Nat) : 1 ≤ digitFuel m := by
  by_cases h : m < 10
  · rw [digitFuel_lt10 h]
    omega
  · rw [digitFuel_ge10 h]
    omega

theorem le_digitFuel (m : Nat) : 1 + m / 10 ≤ digitFuel m := by
  by_cases h : m < 10
  · rw [digitFuel_lt10 h]
    omega
  · rw [digitFuel_ge10 h]
    omega

/-- **The digit loop, executed.** From `n = m ≠ 0` (`m < 2^63`), end-pointer
`p0`, the writable descending window and `digitFuel m` clock, the WHILE-loop
`while (n) { digitBody }` terminates normally having rendered `natToDec m` at
`[p0 - L, p0)`. Strong induction on `m` (each iteration divides by 10). -/
theorem digitLoop_sem (o : Oracle σ) (m : Nat) (p0 : Word) (s : PancakeState σ)
    (hm0 : m ≠ 0) (hm63 : m < 2 ^ 63)
    (hn : s.locals "n" = some (BitVec.ofNat 64 m))
    (hp : s.locals "p" = some p0)
    (hdm : ∀ j, j < (natToDec m).length →
      s.memaddrs (byteAlign (p0 - BitVec.ofNat 64 (j + 1))) = true)
    (hclk : digitFuel m ≤ s.clock) :
    ∃ s', PancakeSem o (.while_ (.var "n") digitBody) s = (none, s') ∧
      s'.clock = s.clock - digitFuel m ∧ RenderPost m p0 s s' := by
  have hgW : eval s (.var "n") = some (BitVec.ofNat 64 m) := hn
  have hwne : (BitVec.ofNat 64 m : Word) ≠ 0 := ofNat64_ne_zero hm0 (by omega)
  have hfpos := digitFuel_pos m
  have hflow := le_digitFuel m
  have hclk0 : s.clock ≠ 0 := by omega
  have hLpos := natToDec_length_pos m
  -- run one body on `dec_clock s`
  obtain ⟨sb, hbody, hbn, hbq, hbp, hbclk, hbmem, hbma, hbbe, hbba, hbfr⟩ :=
    digitBody_sem o (m := m) (p0 := p0) (s := decClock s) hn hp hm63 (hdm 0 hLpos)
      (by show m / 10 ≤ s.clock - 1; omega)
  replace hbclk : sb.clock = s.clock - 1 - m / 10 := hbclk
  replace hbmem : sb.memory = putByte s.memory s.be (p0 - BitVec.ofNat 64 1)
      (digitByte (m % 10)) := hbmem
  replace hbma : sb.memaddrs = s.memaddrs := hbma
  replace hbbe : sb.be = s.be := hbbe
  replace hbba : sb.baseAddr = s.baseAddr := hbba
  have hbfr' : ∀ key, key ≠ "n" → key ≠ "q" → key ≠ "p" → sb.locals key = s.locals key :=
    fun key h1 h2 h3 => hbfr key h1 h2 h3
  have hstep := while_iter_le o hgW hwne hclk0 hbody (by omega)
  by_cases hm10 : m < 10
  · -- single digit: the loop exits at `sb`
    have hq0 : m / 10 = 0 := Nat.div_eq_of_lt hm10
    have hexitg : eval sb (.var "n") = some (0 : Word) := by
      show sb.locals "n" = some (0 : Word)
      rw [hbn, hq0]
      rfl
    refine ⟨sb, ?_, ?_, ?_⟩
    · rw [hstep]
      exact while_exit o hexitg
    · rw [hbclk, digitFuel_lt10 hm10]
      omega
    · exact single_digit_post hm10 hbn hbp hbmem hbma hbbe hbba hbfr' (hdm 0 hLpos)
  · -- multi digit: recurse on the quotient with end-pointer `p0 - 1`
    have hmq0 : m / 10 ≠ 0 := by omega
    have hmq63 : m / 10 < 2 ^ 63 := by omega
    have hLm : (natToDec m).length = (natToDec (m / 10)).length + 1 := by
      rw [natToDec_split (by omega : 10 ≤ m)]
      simp
    have hdm' : ∀ j, j < (natToDec (m / 10)).length →
        sb.memaddrs (byteAlign ((p0 - BitVec.ofNat 64 1) - BitVec.ofNat 64 (j + 1)))
          = true := by
      intro j hj
      rw [hbma, ← sub_ofNat_succ]
      exact hdm (j + 1) (by omega)
    have hclkq : digitFuel (m / 10) ≤ sb.clock := by
      rw [hbclk]
      have hge := digitFuel_ge10 hm10
      omega
    obtain ⟨s', hrun, hclk', hpost⟩ :=
      digitLoop_sem o (m / 10) (p0 - BitVec.ofNat 64 1) sb hmq0 hmq63 hbn hbp hdm' hclkq
    refine ⟨s', ?_, ?_, ?_⟩
    · rw [hstep]
      exact hrun
    · rw [hclk', hbclk, digitFuel_ge10 hm10]
      omega
    · exact multi_digit_post (by omega) hm63 hbmem hbma hbbe hbba hbfr' (hdm 0 hLpos) hpost
termination_by m
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-! ## 6. `natToDecProg` — the FULL `natToDec` as one Pancake program -/

/-- Clock budget of the whole render: the unguarded first `digitBody` plus (if
more digits remain) the loop's budget. -/
def natFuel (m : Nat) : Nat :=
  m / 10 + (if m / 10 = 0 then 0 else digitFuel (m / 10))

/-- `natToDec` as a REAL Pancake program (do-while — every `m`, including 0,
emits at least one digit, matching `natToDec 0 = "0"`):
`digitBody; while (n) { digitBody }`. Subset check: `Assign`/`Seq`/`While`/
`StoreByte`, guards `Var`/`Cmp NotLess`, ops `Op Sub`/`Op Add` — every
construct is in the modelled panLang region subset; NO Div/Mod anywhere. -/
def natToDecProg : PancakeProg :=
  .seq digitBody (.while_ (.var "n") digitBody)

/-- **The full multi-digit render, executed.** From `n = m` (`m < 2^63`),
end-pointer `p0`, the `L = (natToDec m).length` writable bytes below `p0` and
`natFuel m` clock: `natToDecProg` terminates normally; the post-state holds the
EXACT `natToDec m` ASCII bytes at `[p0 - L, p0)` (most-significant first),
`p = p0 - L`, `n = 0`; every other byte, local and state field is framed.

This closes the natToDec residual: with `natToDec_readback` (the digits read
back as `m`) and the `Nat.repr` guard corpus, the byte content of the
status-line/length render is now a compiled-and-proven Pancake program. -/
theorem natToDecProg_sem (o : Oracle σ) (m : Nat) (p0 : Word) (s : PancakeState σ)
    (hm63 : m < 2 ^ 63)
    (hn : s.locals "n" = some (BitVec.ofNat 64 m))
    (hp : s.locals "p" = some p0)
    (hdm : ∀ j, j < (natToDec m).length →
      s.memaddrs (byteAlign (p0 - BitVec.ofNat 64 (j + 1))) = true)
    (hclk : natFuel m ≤ s.clock) :
    ∃ s', PancakeSem o natToDecProg s = (none, s') ∧
      s'.clock = s.clock - natFuel m ∧ RenderPost m p0 s s' := by
  have hLpos := natToDec_length_pos m
  have hnf : m / 10 ≤ natFuel m := by
    unfold natFuel
    split <;> omega
  obtain ⟨sb, hbody, hbn, hbq, hbp, hbclk, hbmem, hbma, hbbe, hbba, hbfr⟩ :=
    digitBody_sem o (m := m) (p0 := p0) (s := s) hn hp hm63 (hdm 0 hLpos)
      (by omega)
  have hprog : PancakeSem o natToDecProg s
      = PancakeSem o (.while_ (.var "n") digitBody) sb :=
    seq_step o hbody (by omega)
  by_cases hm10 : m < 10
  · -- one digit; the trailing while exits immediately
    have hq0 : m / 10 = 0 := Nat.div_eq_of_lt hm10
    have hexitg : eval sb (.var "n") = some (0 : Word) := by
      show sb.locals "n" = some (0 : Word)
      rw [hbn, hq0]
      rfl
    have hnf0 : natFuel m = m / 10 := by
      unfold natFuel
      rw [if_pos hq0]
      omega
    refine ⟨sb, ?_, ?_, ?_⟩
    · rw [hprog]
      exact while_exit o hexitg
    · rw [hbclk, hnf0]
    · exact single_digit_post hm10 hbn hbp hbmem hbma hbbe hbba hbfr (hdm 0 hLpos)
  · -- more digits: the trailing while renders the quotient below `p0 - 1`
    have hmq0 : m / 10 ≠ 0 := by omega
    have hmq63 : m / 10 < 2 ^ 63 := by omega
    have hLm : (natToDec m).length = (natToDec (m / 10)).length + 1 := by
      rw [natToDec_split (by omega : 10 ≤ m)]
      simp
    have hdm' : ∀ j, j < (natToDec (m / 10)).length →
        sb.memaddrs (byteAlign ((p0 - BitVec.ofNat 64 1) - BitVec.ofNat 64 (j + 1)))
          = true := by
      intro j hj
      rw [hbma, ← sub_ofNat_succ]
      exact hdm (j + 1) (by omega)
    have hnfq : natFuel m = m / 10 + digitFuel (m / 10) := by
      unfold natFuel
      rw [if_neg hmq0]
    have hclkq : digitFuel (m / 10) ≤ sb.clock := by
      rw [hbclk]
      omega
    obtain ⟨s', hrun, hclk', hpost⟩ :=
      digitLoop_sem o (m / 10) (p0 - BitVec.ofNat 64 1) sb hmq0 hmq63 hbn hbp hdm' hclkq
    refine ⟨s', ?_, ?_, ?_⟩
    · rw [hprog]
      exact hrun
    · rw [hclk', hbclk, hnfq]
      omega
    · exact multi_digit_post (by omega) hm63 hbmem hbma hbbe hbba hbfr (hdm 0 hLpos) hpost

/-! ## 7. Corpus (theorem-level, ): 404 and the 0 edge -/

example : natToDec 404 = [52, 48, 52] := by decide
example : natToDec 0 = [48] := by decide

/-- "404": the three status bytes land at `p0-3, p0-2, p0-1` as `'4' '0' '4'`. -/
example (o : Oracle σ) (s : PancakeState σ) (p0 : Word)
    (hn : s.locals "n" = some (BitVec.ofNat 64 404))
    (hp : s.locals "p" = some p0)
    (hdm : ∀ j, j < 3 → s.memaddrs (byteAlign (p0 - BitVec.ofNat 64 (j + 1))) = true)
    (hclk : 46 ≤ s.clock) :
    ∃ s', PancakeSem o natToDecProg s = (none, s') ∧
      memLoadByte s'.memory s'.memaddrs s'.be (p0 - BitVec.ofNat 64 3) = some 52 ∧
      memLoadByte s'.memory s'.memaddrs s'.be (p0 - BitVec.ofNat 64 2) = some 48 ∧
      memLoadByte s'.memory s'.memaddrs s'.be (p0 - BitVec.ofNat 64 1) = some 52 := by
  have hlist : natToDec 404 = [52, 48, 52] := by decide
  have hlen : (natToDec 404).length = 3 := by rw [hlist]; rfl
  have hf40 : digitFuel 40 = 6 := by
    rw [digitFuel_ge10 (by omega)]
    show 1 + 40 / 10 + digitFuel (40 / 10) = 6
    rw [show (40 : Nat) / 10 = 4 from rfl, digitFuel_lt10 (by omega : (4 : Nat) < 10)]
  have hfuel : natFuel 404 = 46 := by
    unfold natFuel
    rw [show (404 : Nat) / 10 = 40 from rfl, if_neg (by omega : ¬ (40 : Nat) = 0), hf40]
  obtain ⟨s', hrun, _, _, _, hbytes, _⟩ :=
    natToDecProg_sem o 404 p0 s (by omega) hn hp
      (by intro j hj; rw [hlen] at hj; exact hdm j hj)
      (by rw [hfuel]; omega)
  refine ⟨s', hrun, ?_, ?_, ?_⟩
  · have h := hbytes 0 52 (by rw [hlist]; rfl)
    rw [hlen] at h
    exact h
  · have h := hbytes 1 48 (by rw [hlist]; rfl)
    rw [hlen] at h
    exact h
  · have h := hbytes 2 52 (by rw [hlist]; rfl)
    rw [hlen] at h
    exact h

/-- The 0 edge: `natToDec 0 = "0"` — the do-while still emits the single byte
`'0'` (48) at `p0 - 1` (a guarded-only `While` would emit nothing). -/
example (o : Oracle σ) (s : PancakeState σ) (p0 : Word)
    (hn : s.locals "n" = some (BitVec.ofNat 64 0))
    (hp : s.locals "p" = some p0)
    (hdm : s.memaddrs (byteAlign (p0 - BitVec.ofNat 64 1)) = true) :
    ∃ s', PancakeSem o natToDecProg s = (none, s') ∧
      memLoadByte s'.memory s'.memaddrs s'.be (p0 - BitVec.ofNat 64 1) = some 48 := by
  have hlen : (natToDec 0).length = 1 := by decide
  obtain ⟨s', hrun, _, _, _, hbytes, _⟩ :=
    natToDecProg_sem o 0 p0 s (by omega) hn hp
      (by intro j hj
          rw [hlen] at hj
          have hj0 : j = 0 := by omega
          subst hj0
          exact hdm)
      (by show natFuel 0 ≤ s.clock
          unfold natFuel
          simp)
  refine ⟨s', hrun, ?_⟩
  have h := hbytes 0 48 (by decide)
  rw [hlen] at h
  exact h

end Pancake.NatToDecFull

-- ASSURANCE: the load-bearing chain uses only the three Lean-core axioms.
#print axioms Pancake.NatToDecFull.digitBody_sem
#print axioms Pancake.NatToDecFull.digitLoop_sem
#print axioms Pancake.NatToDecFull.natToDecProg_sem
#print axioms Pancake.NatToDecFull.natToDec_split
