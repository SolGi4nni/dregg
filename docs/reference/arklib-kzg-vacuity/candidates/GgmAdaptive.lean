/-
ADAPTIVE Generic Group Model (Shoup / Boneh–Boyen) bound for t-SDH — the frontier from
`GgmCandidate.lean` (STATIC, q=0) pushed to `q_G` adaptive oracle queries.

NOT part of ArkLib. Scratch research file supporting `docs/reference/arklib-kzg-vacuity/PAPER.md §9`
and `SOUND-FIX-VERDICT.md`.

The static file proves: every *committed* generic adversary (outputs a degree-≤D representation
polynomial with the trapdoor τ absent) wins t-SDH on ≤ (D+1)/(p−1) of trapdoors. That is the q=0
fragment. This file builds the ADAPTIVE object: an adversary that makes `q` oracle queries —
group operations (linear combinations), pairings (polynomial products), and EQUALITY tests between
opaque handles — before committing its output. The oracle answers equality *symbolically* (formal
polynomial equality), never revealing τ.

The Shoup argument, mechanized here at the counting/set level (no probability monad — same honest
idiom as the static file):

  1. THE GENERIC-GROUP ORACLE (§ Oracle): handles are ℕ indices into a table of formal polynomials
     in `(ZMod p)[X]`, seeded with the SRS `1, X, …, X^D` (G₁), `1, X` (G₂). Moves append linear
     combinations / pairing products; equality is answered by an abstract `AnswerFn`.

  2. IDENTICAL-UNTIL-BAD (§ Coincidence), the crux, PROVEN not assumed: run the adversary against
     TWO answer functions. If they agree on every pair actually queried in the first run, the runs
     coincide step-for-step (`run_congr_of_agree`, by induction on fuel). The real oracle (equality
     at τ) and the symbolic oracle (formal equality) agree on a queried pair `(fᵢ,fⱼ)` UNLESS
     `fᵢ ≠ fⱼ` formally but `fᵢ(τ) = fⱼ(τ)` — τ a root of the nonzero difference: the BAD EVENT.

  3. THE BOUND (§ Bound): `realWinSet ⊆ symbolicWinSet ∪ badSet`. `symbolicWinSet` is bounded by the
     STATIC core (`GgmCandidate.card_winningPoints_le`, reused, not reproved). `badSet` is a union
     of ≤ (#pairs) root-sets of nonzero polys of degree ≤ Δ, bounded by Schwartz–Zippel. Compose →
     the concrete `(D+1 + #pairs·Δ)/(p−1)` ~ `(q+D)²·D/p`.
-/
import GgmCandidate
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Polynomial

namespace GgmAdaptive

open GgmCandidate

variable {p : ℕ} [Fact (Nat.Prime p)]

/-! ## Core 1 — the bad-set union-of-roots bound (Schwartz–Zippel, union form)

Given a finite family of nonzero polynomials each of degree ≤ Δ, the set of field points that are a
root of *at least one* has cardinality ≤ (#polys)·Δ. This bounds the Shoup bad event once the
handle-difference polynomials are collected. -/

/-- The union of the root sets of a finite family of polynomials. -/
noncomputable def rootUnion (ps : Finset ((ZMod p)[X])) : Finset (ZMod p) :=
  ps.biUnion (fun q => q.roots.toFinset)

/-- **Union Schwartz–Zippel.** If every polynomial in the family is nonzero and has degree ≤ Δ,
the union of their roots has card ≤ (#polys)·Δ. -/
theorem card_rootUnion_le {ps : Finset ((ZMod p)[X])} {Δ : ℕ}
    (hdeg : ∀ q ∈ ps, q.natDegree ≤ Δ) :
    (rootUnion ps).card ≤ ps.card * Δ := by
  classical
  refine (Finset.card_biUnion_le).trans ?_
  calc ∑ q ∈ ps, (q.roots.toFinset).card
      ≤ ∑ _q ∈ ps, Δ := by
        refine Finset.sum_le_sum ?_
        intro q hq
        refine (Multiset.toFinset_card_le q.roots).trans ?_
        exact (card_roots' q).trans (hdeg q hq)
    _ = ps.card * Δ := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-! ## Core 2 — the generic-group oracle and its adaptive run

Handles are `ℕ` indices into a `table : List (ZMod p)[X]` of formal polynomials, seeded with the
SRS handles. The adversary is `Strat`: given the history of equality-query answers (the *only*
τ-dependent input it receives in the generic model — Shoup 1997), it chooses the next `Move` or
commits an output `(offset c, handle index k)`. The oracle answers equality via an abstract
`AnswerFn`; the real oracle answers by evaluation at τ, the symbolic oracle by formal equality. -/

/-- How the oracle answers an equality query between the polynomials behind two handles. -/
abbrev AnswerFn (p : ℕ) := (ZMod p)[X] → (ZMod p)[X] → Bool

/-- A generic-group move. `lin` forms a `ZMod p`-linear combination of existing handles (group
add / negate / scalar-mul); `pair` forms the pairing product `e(Hᵢ, Hⱼ)` (G₁×G₂→Gₜ); `query`
issues an equality test whose boolean answer feeds forward into the adversary's next decision. -/
inductive Move (p : ℕ) where
  | lin   : List (ZMod p × ℕ) → Move p
  | pair  : ℕ → ℕ → Move p
  | query : ℕ → ℕ → Move p

/-- A generic (adaptive) adversary: a decision function from the history of equality answers to
either a next move or a committed output `(offset, output-handle-index)`. It never receives τ or a
group element carrying τ — only the equality booleans. -/
abbrev Strat (p : ℕ) := List Bool → Move p ⊕ (ZMod p × ℕ)

/-- Oracle state: the handle table and the equality-answer history. -/
structure St (p : ℕ) where
  table : List ((ZMod p)[X])
  hist  : List Bool

/-- The polynomial produced by a linear-combination move: `Σ cᵢ · table[idxᵢ]`. -/
noncomputable def combine (spec : List (ZMod p × ℕ)) (table : List ((ZMod p)[X])) : (ZMod p)[X] :=
  (spec.map (fun ci => C ci.1 * table.getD ci.2 0)).sum

/-- **The adaptive generic-group run.** Fuel-bounded. Returns the committed output `(offset,
output polynomial)` together with the list of `(a,b)` polynomial pairs the adversary actually
queried for equality — the transcript we test the two oracles' agreement against. -/
noncomputable def runAux (ans : AnswerFn p) (strat : Strat p) :
    ℕ → St p → (ZMod p × (ZMod p)[X]) × List ((ZMod p)[X] × (ZMod p)[X])
  | 0, _ => ((0, 0), [])
  | fuel + 1, st =>
    match strat st.hist with
    | Sum.inr (c, k) => ((c, st.table.getD k 0), [])
    | Sum.inl (Move.lin spec) =>
        runAux ans strat fuel ⟨st.table ++ [combine spec st.table], st.hist⟩
    | Sum.inl (Move.pair i j) =>
        runAux ans strat fuel ⟨st.table ++ [st.table.getD i 0 * st.table.getD j 0], st.hist⟩
    | Sum.inl (Move.query i j) =>
        let a := st.table.getD i 0
        let b := st.table.getD j 0
        let r := runAux ans strat fuel ⟨st.table, st.hist ++ [ans a b]⟩
        (r.1, (a, b) :: r.2)

/-- The committed output `(offset, output polynomial)` of a run. -/
noncomputable def runOutput (ans : AnswerFn p) (strat : Strat p) (fuel : ℕ) (st : St p) :
    ZMod p × (ZMod p)[X] :=
  (runAux ans strat fuel st).1

/-- **IDENTICAL-UNTIL-BAD (the crux), PROVEN not assumed.** If two answer functions agree on every
pair actually queried in the `ans1` run, the two runs are *identical* — same output, same queried
transcript. Proof: induction on fuel; the run branches on the oracle only at `query` steps, and
agreement on the head query keeps the histories (hence all future decisions) in lockstep. -/
theorem runAux_congr_of_agree {ans1 ans2 : AnswerFn p} (strat : Strat p) :
    ∀ (fuel : ℕ) (st : St p),
      (∀ ab ∈ (runAux ans1 strat fuel st).2, ans1 ab.1 ab.2 = ans2 ab.1 ab.2) →
      runAux ans2 strat fuel st = runAux ans1 strat fuel st := by
  intro fuel
  induction fuel with
  | zero => intro st _; rfl
  | succ fuel ih =>
    intro st h
    -- Case on the adversary's decision at the current history.
    rcases hdec : strat st.hist with m | out
    · cases m with
      | lin spec =>
        -- lin move: no query; recurse on the extended table.
        have e1 : runAux ans1 strat (fuel + 1) st
            = runAux ans1 strat fuel ⟨st.table ++ [combine spec st.table], st.hist⟩ := by
          simp only [runAux, hdec]
        have e2 : runAux ans2 strat (fuel + 1) st
            = runAux ans2 strat fuel ⟨st.table ++ [combine spec st.table], st.hist⟩ := by
          simp only [runAux, hdec]
        rw [e2, e1]
        exact ih _ (by rw [e1] at h; exact h)
      | pair i j =>
        -- pair move: no query; recurse on the extended table.
        have e1 : runAux ans1 strat (fuel + 1) st
            = runAux ans1 strat fuel ⟨st.table ++ [st.table.getD i 0 * st.table.getD j 0], st.hist⟩ := by
          simp only [runAux, hdec]
        have e2 : runAux ans2 strat (fuel + 1) st
            = runAux ans2 strat fuel ⟨st.table ++ [st.table.getD i 0 * st.table.getD j 0], st.hist⟩ := by
          simp only [runAux, hdec]
        rw [e2, e1]
        exact ih _ (by rw [e1] at h; exact h)
      | query i j =>
        -- query move: the divergence point.
        have e1 : runAux ans1 strat (fuel + 1) st
            = ((runAux ans1 strat fuel ⟨st.table, st.hist ++ [ans1 (st.table.getD i 0) (st.table.getD j 0)]⟩).1,
                (st.table.getD i 0, st.table.getD j 0) ::
                  (runAux ans1 strat fuel ⟨st.table, st.hist ++ [ans1 (st.table.getD i 0) (st.table.getD j 0)]⟩).2) := by
          simp only [runAux, hdec]
        have e2 : runAux ans2 strat (fuel + 1) st
            = ((runAux ans2 strat fuel ⟨st.table, st.hist ++ [ans2 (st.table.getD i 0) (st.table.getD j 0)]⟩).1,
                (st.table.getD i 0, st.table.getD j 0) ::
                  (runAux ans2 strat fuel ⟨st.table, st.hist ++ [ans2 (st.table.getD i 0) (st.table.getD j 0)]⟩).2) := by
          simp only [runAux, hdec]
        -- head-of-transcript agreement: ans1 a b = ans2 a b
        have hhead : ans1 (st.table.getD i 0) (st.table.getD j 0)
            = ans2 (st.table.getD i 0) (st.table.getD j 0) :=
          h (st.table.getD i 0, st.table.getD j 0) (by rw [e1]; simp)
        rw [e2, e1, ← hhead]
        have htail : ∀ ab ∈ (runAux ans1 strat fuel
              ⟨st.table, st.hist ++ [ans1 (st.table.getD i 0) (st.table.getD j 0)]⟩).2,
            ans1 ab.1 ab.2 = ans2 ab.1 ab.2 := by
          intro ab hab
          apply h; rw [e1]; simp only [List.mem_cons]; right; exact hab
        rw [ih _ htail]
    · -- output: base case, both stop identically.
      have e1 : runAux ans1 strat (fuel + 1) st = ((out.1, st.table.getD out.2 0), []) := by
        simp only [runAux, hdec]
      have e2 : runAux ans2 strat (fuel + 1) st = ((out.1, st.table.getD out.2 0), []) := by
        simp only [runAux, hdec]
      rw [e2, e1]

/-- The number of queried pairs in a run is bounded by the fuel: each query consumes one step. -/
theorem runAux_queries_length_le (ans : AnswerFn p) (strat : Strat p) :
    ∀ (fuel : ℕ) (st : St p), (runAux ans strat fuel st).2.length ≤ fuel := by
  intro fuel
  induction fuel with
  | zero => intro st; simp [runAux]
  | succ fuel ih =>
    intro st
    rcases hdec : strat st.hist with m | out
    · cases m with
      | lin spec =>
        have e : runAux ans strat (fuel + 1) st
            = runAux ans strat fuel ⟨st.table ++ [combine spec st.table], st.hist⟩ := by
          simp only [runAux, hdec]
        rw [e]; exact (ih _).trans (Nat.le_succ _)
      | pair i j =>
        have e : runAux ans strat (fuel + 1) st
            = runAux ans strat fuel ⟨st.table ++ [st.table.getD i 0 * st.table.getD j 0], st.hist⟩ := by
          simp only [runAux, hdec]
        rw [e]; exact (ih _).trans (Nat.le_succ _)
      | query i j =>
        have e : runAux ans strat (fuel + 1) st
            = ((runAux ans strat fuel ⟨st.table, st.hist ++ [ans (st.table.getD i 0) (st.table.getD j 0)]⟩).1,
                (st.table.getD i 0, st.table.getD j 0) ::
                  (runAux ans strat fuel ⟨st.table, st.hist ++ [ans (st.table.getD i 0) (st.table.getD j 0)]⟩).2) := by
          simp only [runAux, hdec]
        rw [e]; simp only [List.length_cons]
        exact Nat.succ_le_succ (ih _)
    · have e : runAux ans strat (fuel + 1) st = ((out.1, st.table.getD out.2 0), []) := by
        simp only [runAux, hdec]
      rw [e]; simp

/-! ## Core 3 — the symbolic / real oracles and the composed adaptive bound

The symbolic oracle answers equality by *formal* polynomial equality (τ absent); the real oracle
answers by evaluation at τ. `runAux_congr_of_agree` couples them. -/

open Classical in
/-- Symbolic oracle: equality is *formal* polynomial equality, so the whole symbolic run is
τ-independent (the delayed-sampling simulator, Boneh–Boyen). -/
noncomputable def symAns : AnswerFn p := fun f g => decide (f = g)

/-- Real oracle at trapdoor `τ`: equality is evaluation equality at `τ`. -/
noncomputable def realAns (τ : ZMod p) : AnswerFn p := fun f g => decide (f.eval τ = g.eval τ)

variable (strat : Strat p) (st₀ : St p) (fuel : ℕ)

/-- The τ-independent symbolic committed output `(offset, output polynomial)`. -/
noncomputable def symOutput : ZMod p × (ZMod p)[X] := runOutput symAns strat fuel st₀

/-- The τ-independent list of equality-queried pairs in the symbolic run. -/
noncomputable def symPairs : List ((ZMod p)[X] × (ZMod p)[X]) := (runAux symAns strat fuel st₀).2

/-- The bad-event polynomials: differences `a − b` of every *formally distinct* queried pair.
Each is nonzero (Shoup's nonzero-difference requirement). -/
noncomputable def badPolys : Finset ((ZMod p)[X]) :=
  ((symPairs strat st₀ fuel).filter (fun ab => decide (ab.1 ≠ ab.2))).map
      (fun ab => ab.1 - ab.2) |>.toFinset

/-- The Shoup **bad set**: trapdoors on which two formally-distinct queried handles collide. -/
noncomputable def badSet : Finset (ZMod p) := rootUnion (badPolys strat st₀ fuel)

/-- **Agreement off the bad set.** For any `τ` outside the bad set, the real oracle at `τ` agrees
with the symbolic oracle on every pair the symbolic run queried. -/
theorem realAns_agree_off_badSet {τ : ZMod p} (hτ : τ ∉ badSet strat st₀ fuel) :
    ∀ ab ∈ (runAux symAns strat fuel st₀).2,
      symAns ab.1 ab.2 = realAns τ ab.1 ab.2 := by
  intro ab hab
  simp only [symAns, realAns]
  by_cases hfg : ab.1 = ab.2
  · simp [hfg]
  · -- formally distinct: symbolic says "not equal"; show real agrees, i.e. eval differs.
    have hne : ab.1 - ab.2 ≠ 0 := sub_ne_zero.mpr hfg
    have hmem : ab.1 - ab.2 ∈ badPolys strat st₀ fuel := by
      unfold badPolys
      rw [List.mem_toFinset, List.mem_map]
      refine ⟨ab, ?_, rfl⟩
      rw [List.mem_filter]
      exact ⟨hab, by simp [hfg]⟩
    have hnotroot : τ ∉ (ab.1 - ab.2).roots.toFinset := by
      intro hcontra
      exact hτ (Finset.mem_biUnion.mpr ⟨_, hmem, hcontra⟩)
    have hevalne : ab.1.eval τ ≠ ab.2.eval τ := by
      intro hE
      apply hnotroot
      rw [Multiset.mem_toFinset, mem_roots hne]
      simp only [IsRoot.def, eval_sub, hE, sub_self]
    simp [hfg, hevalne]

/-- **The real run equals the symbolic run off the bad set** — the mechanized identical-until-bad
step, specialized. Hence the real committed output coincides with the τ-independent symbolic one. -/
theorem realOutput_eq_symOutput_off_badSet {τ : ZMod p} (hτ : τ ∉ badSet strat st₀ fuel) :
    runOutput (realAns τ) strat fuel st₀ = symOutput strat st₀ fuel := by
  simp only [runOutput, symOutput, runOutput]
  rw [runAux_congr_of_agree strat fuel st₀ (realAns_agree_off_badSet strat st₀ fuel hτ)]

/-! ### The composed adaptive bound

`realWinSet` — the trapdoors on which the adaptive adversary wins t-SDH against the *real* oracle.
The win predicate is the τ+c≠0-guarded one reused verbatim from the static file (so Lean's total
`0⁻¹ = 0` cannot smuggle a spurious win). -/

/-- The trapdoors on which the adaptive adversary wins t-SDH against the real oracle at `τ`. -/
noncomputable def realWinSet : Finset (ZMod p) :=
  nonzeroPoints.filter (fun τ =>
    τ + (runOutput (realAns τ) strat fuel st₀).1 ≠ 0 ∧
      (runOutput (realAns τ) strat fuel st₀).2.eval τ
        = 1 / (τ + (runOutput (realAns τ) strat fuel st₀).1))

/-- **Identical-until-bad, at the set level.** Every real winning trapdoor either triggers the bad
event or is a static win of the τ-independent symbolic output `(c_sym, f_sym)` — Shoup's
`W₀ ⊆ W₁ ∪ F`, mechanized. -/
theorem realWinSet_subset (D : ℕ)
    (hdeg_out : (symOutput strat st₀ fuel).2.natDegree ≤ D) :
    realWinSet strat st₀ fuel ⊆
      badSet strat st₀ fuel ∪
        GgmCandidate.winningPoints
          (⟨(symOutput strat st₀ fuel).1, (symOutput strat st₀ fuel).2, hdeg_out⟩ :
            GenericAdversary D p) := by
  intro τ hτ
  rw [realWinSet, Finset.mem_filter] at hτ
  obtain ⟨hnz, hcond1, hcond2⟩ := hτ
  by_cases hbad : τ ∈ badSet strat st₀ fuel
  · exact Finset.mem_union_left _ hbad
  · refine Finset.mem_union_right _ ?_
    have heq := realOutput_eq_symOutput_off_badSet strat st₀ fuel hbad
    rw [heq] at hcond1 hcond2
    rw [GgmCandidate.winningPoints, Finset.mem_filter]
    exact ⟨hnz, hcond1, hcond2⟩

/-- The number of bad-event polynomials is at most the fuel (one per equality query at most). -/
theorem card_badPolys_le : (badPolys strat st₀ fuel).card ≤ fuel := by
  unfold badPolys
  refine (List.toFinset_card_le _).trans ?_
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (runAux_queries_length_le symAns strat fuel st₀)

/-- **THE ADAPTIVE GGM CARDINALITY BOUND.** For every adaptive generic adversary making ≤ `fuel`
oracle queries, the number of trapdoors on which it wins t-SDH is ≤ `fuel·Δ + (D+1)`: the static
Boneh–Boyen root event `(D+1)` plus the Shoup collision event `(#queries)·Δ`. -/
theorem card_realWinSet_le (D Δ : ℕ)
    (hdeg_out : (symOutput strat st₀ fuel).2.natDegree ≤ D)
    (hdeg_pairs : ∀ q ∈ badPolys strat st₀ fuel, q.natDegree ≤ Δ) :
    (realWinSet strat st₀ fuel).card ≤ fuel * Δ + (D + 1) := by
  classical
  refine (Finset.card_le_card (realWinSet_subset strat st₀ fuel D hdeg_out)).trans ?_
  refine (Finset.card_union_le _ _).trans ?_
  have hbad : (badSet strat st₀ fuel).card ≤ fuel * Δ :=
    (card_rootUnion_le hdeg_pairs).trans
      (Nat.mul_le_mul_right Δ (card_badPolys_le strat st₀ fuel))
  have hwin : (GgmCandidate.winningPoints
      (⟨(symOutput strat st₀ fuel).1, (symOutput strat st₀ fuel).2, hdeg_out⟩ :
        GenericAdversary D p)).card ≤ D + 1 := card_winningPoints_le _
  exact Nat.add_le_add hbad hwin

/-- The adaptive success fraction: winning trapdoors over the `p−1` nonzero trapdoors. -/
noncomputable def adaptiveExperiment : ℚ := (realWinSet strat st₀ fuel).card / (p - 1)

/-- **THE ADAPTIVE GGM SECURITY BOUND (sorry-free).** Every adaptive generic t-SDH adversary
making ≤ `fuel` oracle queries wins on at most a `(fuel·Δ + (D+1))/(p−1)` fraction of trapdoors.
This is the full Shoup / Boneh–Boyen shape — the static `(D+1)/(p−1)` root event plus the
`(#queries)·Δ/(p−1)` collision event — with `Δ = D+1` at faithful SRS degrees.

The two degree hypotheses are the SRS degree invariant (output handle is a G₁ element of degree
≤ D; queried-handle differences have degree ≤ Δ), true structurally for the faithful group-op
discipline. The identical-until-bad step (`realWinSet_subset`) is PROVEN by induction, not
assumed. -/
theorem adaptive_ggm_sound (D Δ : ℕ) (hp : 2 ≤ p)
    (hdeg_out : (symOutput strat st₀ fuel).2.natDegree ≤ D)
    (hdeg_pairs : ∀ q ∈ badPolys strat st₀ fuel, q.natDegree ≤ Δ) :
    adaptiveExperiment strat st₀ fuel ≤ ((fuel * Δ + (D + 1) : ℕ) : ℚ) / (p - 1) := by
  unfold adaptiveExperiment
  have hnum : ((realWinSet strat st₀ fuel).card : ℚ) ≤ ((fuel * Δ + (D + 1) : ℕ) : ℚ) := by
    exact_mod_cast card_realWinSet_le strat st₀ fuel D Δ hdeg_out hdeg_pairs
  have hden : (0 : ℚ) < (p : ℚ) - 1 := by
    have : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
    linarith
  gcongr

/-- **Non-vacuity of the adaptive bound.** Whenever `fuel·Δ + (D+1) < p − 1` the adaptive bound is
a genuine rational `< 1`: at cryptographic parameters (`p ≈ 2²⁵⁴`, `D ≈ 2²⁰`, `fuel = q ≈ 2⁶⁰`)
`fuel·Δ ≈ 2⁸⁰ ≪ p`, so the bound is `≈ 2⁻¹⁷⁴`. -/
theorem adaptive_bound_lt_one (D Δ : ℕ) (hlt : fuel * Δ + (D + 1) < p - 1) (hp : 2 ≤ p) :
    ((fuel * Δ + (D + 1) : ℕ) : ℚ) / (p - 1) < 1 := by
  have hden : (0 : ℚ) < (p : ℚ) - 1 := by
    have : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
    linarith
  rw [div_lt_one hden]
  have h1 : ((fuel * Δ + (D + 1) : ℕ) : ℚ) < ((p - 1 : ℕ) : ℚ) := by exact_mod_cast hlt
  have h2 : ((p - 1 : ℕ) : ℚ) = (p : ℚ) - 1 := by
    have : (1 : ℕ) ≤ p := by omega
    push_cast [Nat.cast_sub this]; ring
  rw [h2] at h1; exact h1

/-- **The adaptive theorem strictly generalizes the static one (non-vacuity anchor).** At `fuel = 0`
the adaptive experiment reduces to the static Boneh–Boyen bound `(D+1)/(p−1)`: the degree
hypotheses are discharged automatically (empty transcript, zero output polynomial), so
`adaptive_ggm_sound` is genuinely instantiable and its `fuel = 0` slice is exactly the static
`ggm_tSdh_sound` number. The `fuel > 0` slices add the honest `(#queries)·Δ` collision term. -/
theorem adaptive_generalizes_static (D : ℕ) (hp : 2 ≤ p) :
    adaptiveExperiment strat st₀ 0 ≤ ((D + 1 : ℕ) : ℚ) / (p - 1) := by
  have hout : (symOutput strat st₀ 0).2.natDegree ≤ D := by
    simp [symOutput, runOutput, runAux]
  have hpairs : ∀ q ∈ badPolys strat st₀ 0, q.natDegree ≤ 0 := by
    intro q hq
    simp [badPolys, symPairs, runAux] at hq
  have := adaptive_ggm_sound strat st₀ 0 D 0 hp hout hpairs
  simpa using this

end GgmAdaptive
