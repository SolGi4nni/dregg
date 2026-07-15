/-
  Pancake/EmitCorrectClock.lean — the CLOCK-ACCOUNTING refinement predicate that
  hosts BOTH straight-line stages AND loop-bearing stages under ONE grammar, and
  the compose rule that lets a loop stage compose with a straight-line frame.
  Additive over Pancake/EmitCorrectLoop.lean (nothing there is modified).

  THE GAP THIS CLOSES. EmitCorrectCompose's `Refines o p φ` is CLOCK-PRESERVING
  and TOTAL: `∀ s, PancakeSem o p s = (none, φ s) ∧ (φ s).clock = s.clock`. A
  loop-bearing stage satisfies neither conjunct — it CONSUMES clock (one tick per
  iteration), and it terminates normally only from states in an invariant with a
  sufficient budget, so it has no total, clock-preserving transformer. That is why
  EmitCorrectLoop proves loop stages in a Hoare-postcondition style (`∃ s', … ∧
  I 0 s'`) that does NOT fit the uniform `Refines` grammar, and a loop stage could
  not compose into it.

  THE PREDICATE (`RefinesClk`, §0). A single predicate that accounts for clock as
  a monotonically-CONSUMED resource and carries a per-stage PRECONDITION:

      RefinesClk o p P Q  :=
        ∀ s, P s → ∃ s', PancakeSem o p s = (none, s') ∧ Q s s' ∧ s'.clock ≤ s.clock

  Two moves generalise `Refines` to loops at once:
   * the `≤` clock accounting (not `=`) hosts a clock-consuming loop, while the
     `s'.clock ≤ s.clock` bookkeeping is EXACTLY what makes every `Seq`/`Dec`
     clock-clamp a no-op, so refinements still compose;
   * the precondition `P` carries the loop's iteration BUDGET (`len ≤ s.clock`) and
     the entry invariant — and, for straight-line stages whose expression only
     evaluates in-context (e.g. `result := acc`, valid only after the loop bound
     `acc`), the enabling precondition too.

  WHAT IS PROVEN (all `#print axioms`-clean, 0 `sorry`):
   * `refinesClk_of_refines`   — every straight-line `Refines` stage is a
                                 `RefinesClk` stage (`P = True`), so the loop-free
                                 Gate-A theory embeds unchanged.
   * `refinesClk_assign`       — a CONDITIONAL straight-line assign (its RHS need
                                 only evaluate under `P`) — the post-loop publish.
   * `refinesClk_seq`          — THE compose rule: a stage and a straight-line
                                 frame (in either order) compose, given a link
                                 `P₁ ∧ Q₁ → P₂`. Clock-clamp discharged by `≤`.
   * `refinesClk_dec`          — the lexical-scope (`Dec`) compose rule.
   * `refinesClk_conseq`       — strengthen precondition / weaken postcondition.
   * `while_inv_cond_clk`      — the reusable bounded-`While` rule, now ALSO
                                 delivering `s'.clock ≤ s.clock` (the clock
                                 accounting `while_inv_cond` did not track).
   * `refinesClk_scanWhile`    — the SCAN loop as ONE `RefinesClk` stage (instance
                                 of `while_inv_cond_clk` at the scan guard/body).
   * `refinesClk_scan_publish` — THE MONEY SHOT: the scan LOOP composed with the
                                 `result := acc` straight-line frame, as a single
                                 `RefinesClk` stage, BY `refinesClk_seq`.
   * `region_via_clock`        — `region_scan_correct` LIFTED into the uniform
                                 rule: the whole loop-bearing `scanElse`
                                 (`Dec acc; Dec i; (scanWhile; result:=acc)`) is a
                                 single `RefinesClk` stage, assembled purely by the
                                 §compose rules — the hand-composition of
                                 EmitCorrectRegion is now an instance of the grammar.

  This is Stack L (the Lean model of Pancake). NO byte/machine claims here.
-/
import Pancake.EmitCorrectLoop

namespace Pancake.EmitCorrectClock

open Pancake Pancake.EmitCorrect Pancake.EmitCorrectCompose Pancake.EmitCorrectLoop

variable {σ : Type}

/-! ## 0. The clock-accounting refinement predicate

`RefinesClk o p P Q`: from any state satisfying the precondition `P`, the emitted
program `p` runs to a NORMAL termination (`result = none`) in a state `s'` related
to the entry by `Q`, having consumed clock MONOTONICALLY (`s'.clock ≤ s.clock`).
Unlike `Refines` this permits clock CONSUMPTION (a loop) and a PRECONDITION (an
invariant + budget, or an enabling context); the `≤` accounting is what keeps the
per-boundary clock-clamps no-ops so the predicate still composes. -/
def RefinesClk (o : Oracle σ) (p : PancakeProg)
    (P : PancakeState σ → Prop) (Q : PancakeState σ → PancakeState σ → Prop) : Prop :=
  ∀ s, P s → ∃ s', PancakeSem o p s = (none, s') ∧ Q s s' ∧ s'.clock ≤ s.clock

/-! ## 1. Straight-line stages embed -/

/-- Every straight-line `Refines` stage is a `RefinesClk` stage with the trivial
precondition: `Refines` gives `(φ s).clock = s.clock`, so the `≤` accounting holds
with equality. The loop-free Gate-A theory (`emit_correct_generic`) thus lives
inside `RefinesClk` unchanged. -/
theorem refinesClk_of_refines (o : Oracle σ) {p : PancakeProg}
    {φ : PancakeState σ → PancakeState σ} (h : Refines o p φ) :
    RefinesClk o p (fun _ => True) (fun s s' => s' = φ s) := by
  intro s _
  obtain ⟨he, hc⟩ := h s
  exact ⟨φ s, he, rfl, Nat.le_of_eq hc⟩

/-- A CONDITIONAL straight-line assign: its RHS need only evaluate to `f s` under
the precondition `P` (e.g. `result := acc`, whose `acc` is bound only after the
loop). Clock is preserved (assign never touches it), so the `≤` accounting holds. -/
theorem refinesClk_assign (o : Oracle σ) (x : String) (e : PancakeExp)
    (P : PancakeState σ → Prop) (f : PancakeState σ → Value)
    (hf : ∀ s, P s → eval s e = some (f s)) :
    RefinesClk o (.assign x e) P
      (fun s s' => s' = { s with locals := setLocal s.locals x (f s) }) := by
  intro s hP
  exact ⟨_, sem_assign (oracle := o) (hf s hP), rfl, Nat.le_refl _⟩

/-! ## 2. The compose rules -/

/-- THE COMPOSE RULE. Two `RefinesClk` stages compose sequentially, given the
link `P₁ ∧ Q₁ → P₂` (the first stage's postcondition enables the second's
precondition). The `Seq` clock-clamp `min s.clock s1.clock` collapses to `s1.clock`
by the `≤` accounting (`hc1 : s1.clock ≤ s.clock`), so the clamped mid-state is
`defeq` to the unclamped one. Works in EITHER order — a loop then a straight-line
frame, or a frame then a loop — since it is symmetric in the stage roles. -/
theorem refinesClk_seq (o : Oracle σ) {p1 p2 : PancakeProg}
    {P1 : PancakeState σ → Prop} {Q1 : PancakeState σ → PancakeState σ → Prop}
    {P2 : PancakeState σ → Prop} {Q2 : PancakeState σ → PancakeState σ → Prop}
    (h1 : RefinesClk o p1 P1 Q1)
    (h2 : RefinesClk o p2 P2 Q2)
    (hlink : ∀ s s1, P1 s → Q1 s s1 → P2 s1) :
    RefinesClk o (.seq p1 p2) P1 (fun s s' => ∃ s1, Q1 s s1 ∧ Q2 s1 s') := by
  intro s hP1
  obtain ⟨s1, he1, hQ1, hc1⟩ := h1 s hP1
  obtain ⟨s2, he2, hQ2, hc2⟩ := h2 s1 (hlink s s1 hP1 hQ1)
  refine ⟨s2, ?_, ⟨s1, hQ1, hQ2⟩, Nat.le_trans hc2 hc1⟩
  have hmin : min s.clock s1.clock = s1.clock := by omega
  rw [sem_seq_none (oracle := o) he1, hmin]
  -- `{ s1 with clock := s1.clock }` is defeq `s1` (structure eta)
  exact he2

/-- The lexical-scope (`Dec`) compose rule. `Dec v e cont` binds `v := eval e`,
runs `cont`, then restores the shadowed binding. Given the bind evaluates under
`P` and the continuation is a `RefinesClk` stage whose precondition `Pc` is
established on the extended scope, the `Dec` is a `RefinesClk` stage. Clock is
untouched by the bind/restore, so `cont`'s `≤` accounting carries through. -/
theorem refinesClk_dec (o : Oracle σ) (v : String) (e : PancakeExp)
    {cont : PancakeProg}
    (P : PancakeState σ → Prop) (f : PancakeState σ → Value)
    (Pc : PancakeState σ → Prop) (Qc : PancakeState σ → PancakeState σ → Prop)
    (hf : ∀ s, P s → eval s e = some (f s))
    (hcont : RefinesClk o cont Pc Qc)
    (hlink : ∀ s, P s → Pc { s with locals := setLocal s.locals v (f s) }) :
    RefinesClk o (.dec v e cont) P
      (fun s s' => ∃ smid,
        Qc { s with locals := setLocal s.locals v (f s) } smid ∧
        s' = { smid with locals := resVar smid.locals v (s.locals v) }) := by
  intro s hP
  obtain ⟨smid, hemid, hQmid, hcmid⟩ := hcont _ (hlink s hP)
  refine ⟨{ smid with locals := resVar smid.locals v (s.locals v) },
    sem_dec (oracle := o) (hf s hP) hemid, ⟨smid, hQmid, rfl⟩, ?_⟩
  -- (restore smid).clock = smid.clock ≤ (bind s).clock = s.clock
  exact hcmid

/-- Consequence: strengthen the precondition and weaken the postcondition of a
`RefinesClk` stage. Lets a composed stage be re-stated with a clean contract. -/
theorem refinesClk_conseq (o : Oracle σ) {p : PancakeProg}
    {P Q} {P' : PancakeState σ → Prop} {Q' : PancakeState σ → PancakeState σ → Prop}
    (h : RefinesClk o p P Q)
    (hP : ∀ s, P' s → P s)
    (hQ : ∀ s s', P' s → Q s s' → Q' s s') :
    RefinesClk o p P' Q' := by
  intro s hP's
  obtain ⟨s', he, hq, hc⟩ := h s (hP s hP's)
  exact ⟨s', he, hQ s s' hP's hq, hc⟩

/-! ## 3. The bounded-`While` rule with clock accounting

`while_inv_cond` (EmitCorrectLoop) delivers `∃ s', … ∧ I 0 s'` but does NOT track
the final clock. `RefinesClk` needs `s'.clock ≤ s.clock`, so we re-run the same
induction adding the clock bound — the body hypothesis already supplies
`s2.clock = s.clock - 1` per step, so the bound telescopes. -/
theorem while_inv_cond_clk (o : Oracle σ) (e : PancakeExp) (body : PancakeProg)
    (I : Nat → PancakeState σ → Prop)
    (hguard : ∀ n s, I n s → eval s e = some (if n = 0 then (0 : Word) else 1))
    (hbody : ∀ n s, I (n + 1) s →
      ∃ s2, PancakeSem o body (decClock s) = (none, s2) ∧ I n s2 ∧ s2.clock = s.clock - 1) :
    ∀ (rem : Nat) (s : PancakeState σ), I rem s → rem ≤ s.clock →
      ∃ s', PancakeSem o (.while_ e body) s = (none, s') ∧ I 0 s' ∧ s'.clock ≤ s.clock := by
  intro rem
  induction rem with
  | zero =>
    intro s hI _
    refine ⟨s, ?_, hI, Nat.le_refl _⟩
    rw [PancakeSem, hguard 0 s hI]; simp
  | succ m ih =>
    intro s hI hclock
    have hclock0 : s.clock ≠ 0 := by omega
    have hcond : eval s e = some (1 : Word) := by
      have := hguard (m + 1) s hI; simpa using this
    obtain ⟨s2, hs2eq, hs2I, hs2clk⟩ := hbody m s hI
    have hmin : min (s.clock - 1) s2.clock = s2.clock := by omega
    have hclamp : ({ s2 with clock := min (s.clock - 1) s2.clock } : PancakeState σ) = s2 := by
      rw [hmin]
    obtain ⟨s', hs'eq, hs'I, hs'clk⟩ := ih s2 hs2I (by omega)
    refine ⟨s', ?_, hs'I, by omega⟩
    rw [PancakeSem]
    simp only [hcond, ne_eq, show ((1 : Word) = 0) = False from by decide, not_false_eq_true,
               if_true, hclock0, if_false, clampClock, hs2eq]
    rw [hclamp]
    exact hs'eq

/-! ## 4. The SCAN loop as one `RefinesClk` stage -/

/-- The scan `While` is a single `RefinesClk` stage: precondition = the entry
invariant (`scanInv` at index `0`, i.e. `acc = 0, i = 0`, view loaded) plus the
iteration budget `len ≤ s.clock`; postcondition = `scanInv 0` (the full digest in
`acc`, `i = len`). Obtained by instantiating `while_inv_cond_clk` at the scan
guard/body (reusing `scan_guard`/`scan_step` from EmitCorrectLoop). -/
theorem refinesClk_scanWhile (o : Oracle σ) (a : List (BitVec 8)) (buf : Word) (off len : Nat)
    (hlen63 : len < 2 ^ 63) :
    RefinesClk o scanWhile
      (fun s => scanInv a buf off len len s ∧ len ≤ s.clock)
      (fun _ s' => scanInv a buf off len 0 s') := by
  intro s hP
  obtain ⟨hI, hclk⟩ := hP
  obtain ⟨s', hs'eq, hs'I, hs'clk⟩ :=
    while_inv_cond_clk o (.cmp .less (.var "i") (.var "len")) scanBody
      (scanInv a buf off len)
      (scan_guard a buf off len hlen63)
      (scan_step o a buf off len hlen63)
      len s hI hclk
  exact ⟨s', hs'eq, hs'I, hs'clk⟩

/-- THE MONEY SHOT: the loop stage `scanWhile` composed with the straight-line
frame `result := acc` is a SINGLE `RefinesClk` stage, assembled by the compose
rule `refinesClk_seq`. The publish frame is CONDITIONAL (its `acc` is bound only
by the loop's postcondition), handled by `refinesClk_assign` + the seq link. This
is a loop-bearing stage composing into the uniform clock-accounting grammar — the
named residual, closed. -/
theorem refinesClk_scan_publish (o : Oracle σ) (a : List (BitVec 8)) (buf : Word) (off len : Nat)
    (hlen63 : len < 2 ^ 63) :
    RefinesClk o (.seq scanWhile (.assign "result" (.var "acc")))
      (fun s => scanInv a buf off len len s ∧ len ≤ s.clock)
      (fun _ s' => ∃ s1, scanInv a buf off len 0 s1 ∧
        s' = { s1 with locals := setLocal s1.locals "result" (BitVec.ofNat 64 (scanFrom a off len 0)) }) := by
  have hAcc : ∀ s : PancakeState σ, scanInv a buf off len 0 s →
      eval s (.var "acc") = some (BitVec.ofNat 64 (scanFrom a off len 0)) := by
    intro s hI
    obtain ⟨k, hk, hacc, _⟩ := hI
    have : k = len := by omega
    subst this; exact hacc
  exact refinesClk_seq o
    (refinesClk_scanWhile o a buf off len hlen63)
    (refinesClk_assign o "result" (.var "acc")
      (fun s => scanInv a buf off len 0 s)
      (fun _ => BitVec.ofNat 64 (scanFrom a off len 0)) hAcc)
    (fun _ _ _ hq => hq)

/-! ## 5. `region_scan_correct` LIFTED into the uniform rule

The whole loop-bearing region `scanElse` (`Dec acc 0; Dec i 0; (scanWhile;
result := acc)`) assembled as a SINGLE `RefinesClk` stage purely by the compose
rules of §2/§4 — no bespoke hand composition. This is exactly the theorem
`region_scan_correct` proves by hand in EmitCorrectRegion, now obtained as an
INSTANCE of the clock-accounting grammar. -/
theorem region_via_clock (o : Oracle σ) (a : List (BitVec 8)) (buf : Word) (off len : Nat)
    (hlen63 : len < 2 ^ 63) :
    RefinesClk o scanElse
      (fun s =>
        s.locals "len" = some (BitVec.ofNat 64 len) ∧
        s.locals "buf" = some buf ∧
        s.locals "off" = some (BitVec.ofNat 64 off) ∧
        ViewBytes s a buf off len ∧
        len ≤ s.clock)
      (fun _ s' => s'.locals "result" = some (BitVec.ofNat 64 (scanFrom a off len 0))) := by
  -- inner body: scanWhile ; result := acc  (the money-shot stage)
  have hbody := refinesClk_scan_publish o a buf off len hlen63
  -- wrap `Dec i 0`
  have hDecI :
      RefinesClk o (.dec "i" (.const (BitVec.ofNat 64 0)) (.seq scanWhile (.assign "result" (.var "acc"))))
        (fun s =>
          s.locals "acc" = some (BitVec.ofNat 64 0) ∧
          s.locals "len" = some (BitVec.ofNat 64 len) ∧
          s.locals "buf" = some buf ∧
          s.locals "off" = some (BitVec.ofNat 64 off) ∧
          ViewBytes s a buf off len ∧
          len ≤ s.clock)
        _ :=
    refinesClk_dec o "i" (.const (BitVec.ofNat 64 0)) _ (fun _ => BitVec.ofNat 64 0) _ _
      (fun _ _ => rfl) hbody
      (by
        rintro s ⟨hacc, hlen, hbuf, hoff, hview, hclk⟩
        refine ⟨⟨0, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩, hclk⟩
        · simpa [setLocal, scanFrom] using hacc
        · simp [setLocal]
        · simpa [setLocal] using hlen
        · simpa [setLocal] using hbuf
        · simpa [setLocal] using hoff
        · intro i hi; have := hview i hi; simpa [setLocal] using this)
  -- wrap `Dec acc 0`
  have hDecAcc :
      RefinesClk o scanElse
        (fun s =>
          s.locals "len" = some (BitVec.ofNat 64 len) ∧
          s.locals "buf" = some buf ∧
          s.locals "off" = some (BitVec.ofNat 64 off) ∧
          ViewBytes s a buf off len ∧
          len ≤ s.clock)
        _ :=
    refinesClk_dec o "acc" (.const (BitVec.ofNat 64 0)) _ (fun _ => BitVec.ofNat 64 0) _ _
      (fun _ _ => rfl) hDecI
      (by
        rintro s ⟨hlen, hbuf, hoff, hview, hclk⟩
        refine ⟨?_, ?_, ?_, ?_, ?_, hclk⟩
        · simp [setLocal]
        · simpa [setLocal] using hlen
        · simpa [setLocal] using hbuf
        · simpa [setLocal] using hoff
        · intro i hi; have := hview i hi; simpa [setLocal] using this)
  -- weaken the nested postcondition down to `result = digest`
  refine refinesClk_conseq o hDecAcc (fun s h => h) ?_
  rintro s s' _ ⟨smidA, ⟨smidI, ⟨s1, _, rfl⟩, rfl⟩, rfl⟩
  have dr1 : ("result" = "acc") = False := by decide
  have dr2 : ("result" = "i") = False := by decide
  simp only [resVar, dr1, dr2, if_false, setLocal, if_true]

end Pancake.EmitCorrectClock
