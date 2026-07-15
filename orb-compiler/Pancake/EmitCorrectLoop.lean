/-
  Pancake/EmitCorrectLoop.lean — extend the proven translator to a LOOP-BEARING
  construct, additively over Pancake/EmitCorrectCompose.lean (nothing there is
  modified or re-proven).

  THE GAP THIS CLOSES. EmitCorrectCompose's `Stage` grammar {prim, seq, cond} is
  LOOP-FREE (its §6 "HONEST GAP"): the total, clock-preserving `Refines`
  predicate cannot host a `While`, because a loop CONSUMES clock and terminates
  normally only under an invariant + iteration budget. §6 states `while_inv` as
  the reusable Hoare-style loop rule, but `while_inv` requires an
  UNCONDITIONALLY-total body (`∀ s, PancakeSem o body s = (none, bodyφ s)`) — a
  condition NO real loop body meets, since any body that reads a local or a byte
  of memory FAILS (`eval = none`) on states where that local is unbound / that
  byte is out of range. The region pilot's `scan_loop` (Pancake/EmitCorrectRegion)
  is exactly such a body (it reads the view bytes), which is why it was a bespoke
  hand induction rather than an instance of `while_inv`.

  WHAT IS ADDED (both `#print axioms`-clean, 0 `sorry`):
   * `while_inv_cond` — the CONDITIONAL bounded-`While` rule: the body need only
     compute-and-advance the invariant FROM invariant states. This is the honest
     reusable loop rule (`while_inv` is its total-body special case), and it is
     what `scan_loop` is an instance of.
   * `scan_loop_via_rule` / `scanWhile_via_rule` — the SCAN `While` (the region's
     rolling-digest loop, the `boundscan` loop) re-certified THROUGH `while_inv_cond`
     instead of a one-off induction: a genuine While-bearing emit-correctness
     result obtained from the reusable rule.
   * `emit_scanLoop` — ties the loop-bearing program to the `emit` translator:
     `scanBody` is `emit scanBodyStage` for a `Stage` built from primitive leaves,
     so the certified loop `.while_ guard (emit scanBodyStage)` is exactly what the
     structural translator emits.

  This is Stack L (the Lean model of Pancake). NO byte/machine claims here.
-/
import Pancake.EmitCorrectCompose

namespace Pancake.EmitCorrectLoop

open Pancake Pancake.EmitCorrect Pancake.EmitCorrectCompose

variable {σ : Type}

/-! ## 1. The reusable CONDITIONAL bounded-`While` rule

`I n s` is the loop invariant with `n` iterations of budget remaining. Unlike
`while_inv`, the body obligation `hbody` is GUARDED by `I (n+1) s`: the body must
compute to a normal state that (a) satisfies `I n`, and (b) has consumed exactly
one tick of clock — but ONLY from states already in the invariant. This is what
lets a memory- or local-reading body (the scan) be a loop instance. Conclusion:
`I rem s` with `rem ≤ s.clock`, the emitted `While` runs to a state satisfying
`I 0`. Generalises `while_inv` (whose unconditional `hbody`/`hstep` give this one)
and `scan_loop`. -/
theorem while_inv_cond (o : Oracle σ) (e : PancakeExp) (body : PancakeProg)
    (I : Nat → PancakeState σ → Prop)
    (hguard : ∀ n s, I n s → eval s e = some (if n = 0 then (0 : Word) else 1))
    (hbody : ∀ n s, I (n + 1) s →
      ∃ s2, PancakeSem o body (decClock s) = (none, s2) ∧ I n s2 ∧ s2.clock = s.clock - 1) :
    ∀ (rem : Nat) (s : PancakeState σ), I rem s → rem ≤ s.clock →
      ∃ s', PancakeSem o (.while_ e body) s = (none, s') ∧ I 0 s' := by
  intro rem
  induction rem with
  | zero =>
    intro s hI _
    refine ⟨s, ?_, hI⟩
    rw [PancakeSem, hguard 0 s hI]
    simp
  | succ m ih =>
    intro s hI hclock
    have hclock0 : s.clock ≠ 0 := by omega
    have hcond : eval s e = some (1 : Word) := by
      have := hguard (m + 1) s hI; simpa using this
    obtain ⟨s2, hs2eq, hs2I, hs2clk⟩ := hbody m s hI
    have hmin : min (s.clock - 1) s2.clock = s2.clock := by rw [hs2clk, Nat.min_self]
    have hclamp : ({ s2 with clock := min (s.clock - 1) s2.clock } : PancakeState σ) = s2 := by
      rw [hmin]  -- `{ s2 with clock := s2.clock } = s2` by structure eta
    obtain ⟨s', hs'eq, hs'I⟩ := ih s2 hs2I (by rw [hs2clk]; omega)
    refine ⟨s', ?_, hs'I⟩
    rw [PancakeSem]
    simp only [hcond, ne_eq, show ((1 : Word) = 0) = False from by decide, not_false_eq_true,
               if_true, hclock0, if_false, clampClock, hs2eq]
    rw [hclamp]
    exact hs'eq

/-! ## 2. The SCAN `While` as a loop instance of `while_inv_cond`

The invariant carries the rolling-digest accumulator relation, the index, the
frame locals, and the `ViewBytes` byte-memory relation (the load_vec FFI
postcondition A0, an EXPLICIT hypothesis — never a `sorry`). `n` = the number of
iterations still to run; the current index is `k = len - n` (threaded as an
existential `k` with `k + n = len`). -/

/-- The scan loop invariant, indexed by remaining iterations `n`. -/
def scanInv (a : List (BitVec 8)) (buf : Word) (off len : Nat)
    (n : Nat) (s : PancakeState σ) : Prop :=
  ∃ k, k + n = len ∧
    s.locals "acc" = some (BitVec.ofNat 64 (scanFrom a off k 0)) ∧
    s.locals "i"   = some (BitVec.ofNat 64 k) ∧
    s.locals "len" = some (BitVec.ofNat 64 len) ∧
    s.locals "buf" = some buf ∧
    s.locals "off" = some (BitVec.ofNat 64 off) ∧
    ViewBytes s a buf off len

/-- The scan guard `i < len` evaluates to `0` exactly when the budget is spent
(`n = 0`, i.e. `i = len`), else `1`. -/
theorem scan_guard (a : List (BitVec 8)) (buf : Word) (off len : Nat)
    (hlen63 : len < 2 ^ 63) (n : Nat) (s : PancakeState σ) (hI : scanInv a buf off len n s) :
    eval s (.cmp .less (.var "i") (.var "len")) = some (if n = 0 then (0 : Word) else 1) := by
  obtain ⟨k, hkn, _, hi, hlen, _, _, _⟩ := hI
  have hk63 : k < 2 ^ 63 := by omega
  have hev : eval s (.cmp .less (.var "i") (.var "len"))
      = some (if signedLt (BitVec.ofNat 64 k) (BitVec.ofNat 64 len) then 1 else 0) := by
    simp only [eval, hi, hlen]
  rw [hev, signedLt_ofNat _ _ hk63 hlen63]
  by_cases hn : n = 0
  · have hkl : k = len := by omega
    subst hkl; simp [hn]
  · have hkl : k < len := by omega
    simp [hn, hkl]

/-- ONE scan iteration advances the invariant: from `scanInv (n+1) s`, running the
`scanBody` on `decClock s` lands in a normal state satisfying `scanInv n`, having
consumed one clock tick. Reuses the region pilot's `eval_body_acc` (the body word
algebra) and the `sem_assign`/`sem_seq_none` reductions. -/
theorem scan_step (o : Oracle σ) (a : List (BitVec 8)) (buf : Word) (off len : Nat)
    (hlen63 : len < 2 ^ 63) (n : Nat) (s : PancakeState σ) (hI : scanInv a buf off len (n + 1) s) :
    ∃ s2, PancakeSem o scanBody (decClock s) = (none, s2) ∧
      scanInv a buf off len n s2 ∧ s2.clock = s.clock - 1 := by
  obtain ⟨k, hkn, hacc, hi, hlen, hbuf, hoff, hview⟩ := hI
  have hklt : k < len := by omega
  have hdl : (decClock s).locals = s.locals := rfl
  -- (1) the digest-update expression evaluates to the next digest word
  have haccE :
      eval (decClock s)
        (.op .and_
          (.op .add (.mul (.var "acc") (.const (BitVec.ofNat 64 31)))
                    (.loadByte (.op .add (.op .add (.var "buf") (.var "off")) (.var "i"))))
          (.const (BitVec.ofNat 64 16777215)))
        = some (BitVec.ofNat 64 (scanFrom a off (k + 1) 0)) :=
    eval_body_acc hklt hlen63 (by rw [hdl]; exact hacc) (by rw [hdl]; exact hi)
      (by rw [hdl]; exact hbuf) (by rw [hdl]; exact hoff)
      (by intro i hi'; have := hview i hi'; simpa [decClock] using this)
  -- (2) the acc-assignment
  obtain ⟨sA, hsA⟩ : ∃ sA : PancakeState σ,
      sA = { decClock s with
             locals := setLocal (decClock s).locals "acc"
                        (BitVec.ofNat 64 (scanFrom a off (k + 1) 0)) } := ⟨_, rfl⟩
  have hA := sem_assign (oracle := o) (x := "acc") haccE
  rw [← hsA] at hA
  -- (3) the index-bump on sA
  have hiE : eval sA (.op .add (.var "i") (.const (BitVec.ofNat 64 1)))
      = some (BitVec.ofNat 64 (k + 1)) := by
    have hsAi : sA.locals "i" = some (BitVec.ofNat 64 k) := by
      rw [hsA]; simp only [setLocal, decClock]; rw [if_neg (by decide)]; exact hi
    show (match eval sA (.var "i"), eval sA (.const (BitVec.ofNat 64 1)) with
          | some x, some y => some (x + y) | _, _ => none) = _
    simp only [eval, hsAi]
    rw [ofNat_add_small _ _ (by omega)]
  obtain ⟨sB, hsB⟩ : ∃ sB : PancakeState σ,
      sB = { sA with locals := setLocal sA.locals "i" (BitVec.ofNat 64 (k + 1)) } := ⟨_, rfl⟩
  have hB := sem_assign (oracle := o) (x := "i") hiE
  rw [← hsB] at hB
  -- (4) the whole body (Seq); clamp is a no-op since assigns keep the clock
  have hclkSA : sA.clock = (decClock s).clock := by rw [hsA]
  have hclampSA : ({ sA with clock := min (decClock s).clock sA.clock } : PancakeState σ) = sA := by
    rw [hclkSA, Nat.min_self, ← hclkSA]
  have hbody : PancakeSem o scanBody (decClock s) = (none, sB) := by
    rw [scanBody, sem_seq_none hA, hclampSA, hB]
  -- (5) transport the invariant to sB (result-index k+1)
  have hne2 : ("acc" = "i") = False := by decide
  have hne3 : ("len" = "i") = False := by decide
  have hne4 : ("len" = "acc") = False := by decide
  have hne5 : ("buf" = "i") = False := by decide
  have hne6 : ("buf" = "acc") = False := by decide
  have hne7 : ("off" = "i") = False := by decide
  have hne8 : ("off" = "acc") = False := by decide
  have hBacc : sB.locals "acc" = some (BitVec.ofNat 64 (scanFrom a off (k + 1) 0)) := by
    rw [hsB, hsA]; simp only [setLocal, decClock, hne2, if_false, if_true]
  have hBi : sB.locals "i" = some (BitVec.ofNat 64 (k + 1)) := by
    rw [hsB]; simp only [setLocal, if_true]
  have hBlen : sB.locals "len" = some (BitVec.ofNat 64 len) := by
    rw [hsB, hsA]; simp only [setLocal, decClock, hne3, hne4, if_false]; exact hlen
  have hBbuf : sB.locals "buf" = some buf := by
    rw [hsB, hsA]; simp only [setLocal, decClock, hne5, hne6, if_false]; exact hbuf
  have hBoff : sB.locals "off" = some (BitVec.ofNat 64 off) := by
    rw [hsB, hsA]; simp only [setLocal, decClock, hne7, hne8, if_false]; exact hoff
  have hBview : ViewBytes sB a buf off len := by
    intro i hi'; have := hview i hi'
    rw [hsB, hsA]; simpa [decClock] using this
  have hBclk : sB.clock = s.clock - 1 := by simp only [hsB, hsA, decClock]
  exact ⟨sB, hbody, ⟨k + 1, by omega, hBacc, hBi, hBlen, hBbuf, hBoff, hBview⟩, hBclk⟩

/-- SCAN LOOP via the reusable rule: from `scanInv rem s` with budget `rem ≤
s.clock`, the emitted scan `While` runs to a state satisfying `scanInv 0` — i.e.
the accumulator holds the FULL digest `scanFrom a off len 0` and `i = len`.
Obtained by instantiating `while_inv_cond` at the scan guard/body. -/
theorem scan_loop_via_rule (o : Oracle σ) (a : List (BitVec 8)) (buf : Word) (off len : Nat)
    (hlen63 : len < 2 ^ 63) :
    ∀ (rem : Nat) (s : PancakeState σ), scanInv a buf off len rem s → rem ≤ s.clock →
      ∃ s', PancakeSem o scanWhile s = (none, s') ∧ scanInv a buf off len 0 s' :=
  while_inv_cond o (.cmp .less (.var "i") (.var "len")) scanBody
    (scanInv a buf off len)
    (scan_guard a buf off len hlen63)
    (scan_step o a buf off len hlen63)

/-- The scan-`While`-bearing emit-correctness result, in the region's vocabulary:
from index `0` (a freshly-declared `acc = 0`, `i = 0`) with the view loaded
(`ViewBytes` = A0) and enough clock, the emitted scan `While` publishes the SPEC
digest into `acc` and leaves `i = len`. This is `scan_loop`'s conclusion, now
obtained from the generic `while_inv_cond` rule. -/
theorem scanWhile_via_rule (o : Oracle σ) (a : List (BitVec 8)) (buf : Word) (off len : Nat)
    (hlen63 : len < 2 ^ 63) (s : PancakeState σ)
    (hclock : len ≤ s.clock)
    (hacc : s.locals "acc" = some (BitVec.ofNat 64 0))
    (hi : s.locals "i" = some (BitVec.ofNat 64 0))
    (hlen : s.locals "len" = some (BitVec.ofNat 64 len))
    (hbuf : s.locals "buf" = some buf)
    (hoff : s.locals "off" = some (BitVec.ofNat 64 off))
    (hview : ViewBytes s a buf off len) :
    ∃ s', PancakeSem o scanWhile s = (none, s') ∧
      s'.locals "acc" = some (BitVec.ofNat 64 (scanFrom a off len 0)) ∧
      s'.locals "i" = some (BitVec.ofNat 64 len) := by
  have hI0 : scanInv a buf off len len s :=
    ⟨0, by omega, by simpa [scanFrom] using hacc, hi, hlen, hbuf, hoff, hview⟩
  obtain ⟨s', hs'eq, k, hk0, hs'acc, hs'i, _, _, _, _⟩ :=
    scan_loop_via_rule o a buf off len hlen63 len s hI0 hclock
  have hkl : k = len := by omega
  subst hkl
  exact ⟨s', hs'eq, hs'acc, hs'i⟩

/-! ## 3. Tie to the `emit` translator

The certified loop is exactly what the structural translator emits: `scanBody` is
`emit scanBodyStage` for a `Stage` assembled from two primitive-leaf `assign`s, so
`.while_ guard (emit scanBodyStage)` is `scanWhile` definitionally. The primitive
leaves' `den` fields are irrelevant to the loop certificate (the loop's semantic
contract is carried by `scanInv`, not by an unconditional `Refines`), so they are
set to the identity placeholder — the point is that the EMITTED PROGRAM the
translator produces for the body is the one the loop rule certifies. -/

/-- The scan body's two leaf programs, named so the `Stage` leaves' field values
are simple identifiers. Definitionally the two `Assign`s of `scanBody`. -/
def scanBodyAccProg : PancakeProg :=
  .assign "acc"
    (.op .and_
      (.op .add (.mul (.var "acc") (.const (BitVec.ofNat 64 31)))
                (.loadByte (.op .add (.op .add (.var "buf") (.var "off")) (.var "i"))))
      (.const (BitVec.ofNat 64 16777215)))

def scanBodyIProg : PancakeProg :=
  .assign "i" (.op .add (.var "i") (.const (BitVec.ofNat 64 1)))

/-- The scan body as a translator `Stage`: two primitive-`assign` leaves in `seq`.
`emit` of it is `scanBody`. -/
def scanBodyStage : Stage σ :=
  .seq (.prim { prog := scanBodyAccProg, den := fun s => s })
       (.prim { prog := scanBodyIProg, den := fun s => s })

/-- The translator emits `scanBody` for `scanBodyStage`, so the loop program the
rule certifies is exactly `.while_ guard (emit scanBodyStage) = scanWhile`. -/
theorem emit_scanLoop :
    (.while_ (.cmp .less (.var "i") (.var "len")) (emit (scanBodyStage (σ := σ)))
      : PancakeProg) = scanWhile := rfl

end Pancake.EmitCorrectLoop
