/-
# `Dregg2.Crypto.CostTactics` — PROOF-PRODUCING automation for the cost-model proofs.

`CostAdversary` grounds `Eff := PolyTime` in a syntactic cost VECTOR (`Cost O = ⟨intr, qry⟩`),
with `cost`/`stepCost` the instrumented interpreters of a `FreeOracle` program and `PolyTime`
the poly-boundedness of the resulting scalar. The hand-proofs that consume it — the two poles
(`bruteForce_not_polyTime`, `idAdv_polyTime_expGame`), the tight-composition overhead
(`polyTime_postMapProg`), and the spine discharge (`Market.WideCommitBoundary`
`stateCommit_binds_from_polyTime`) — repeat a small vocabulary: reduce a `cost (prog …)` to a
concrete `⟨intr, qry⟩`, then argue a `Nat`-polynomial (or its exp-dominated negation), then apply
the composition lemma. This module packages that vocabulary as three tactics.

  * **`cost_simp`** — the cost NORMAL FORM. `simp only [cost_norm, …]` over the `FreeOracle`
    constructors/combinators (`pure`/`tick`/`query`/`tickN`/`reshape`/`probe`) and the `Cost`
    projections, reducing `cost sz prog` / `(cost sz prog).intr` / `.qry o` / `.total` to a
    concrete arithmetic expression. A REDUCTION driven by the program's syntax — never an
    assertion. Optional `[extra]` lemmas (to unfold a game's own `sz`/adversary defs) and `at h`.

  * **`poly_bound`** — the `Nat`-polynomial closer. Discharges `PolyBoundedNat e` and
    `∃ C k, ∀ l …, e ≤ C·lᵏ + C` for the concrete `e` `cost_simp` produces, by recursing through
    the closure lemmas (`polyBoundedNat_add`/`_const`/`_const_mul`, monomials). The EXP pole is a
    first-class lemma `exp_dominates_not_poly` (via `expBound_not_ppt`), so `bruteForce`'s
    `2^l + l ≤ C·lᵏ + C` is refuted in one step. Proof-producing: if the shape is not poly it
    FAILS, never fabricates.

  * **`poly_time`** — the efficiency-preservation one-shot. `poly_time f cw bw co bo hA` proves
    `IsPolyTime sz' (Adversary.postMap (fun _ => rfl) f A)` from `hA : IsPolyTime sz A` by applying
    `isPolyTime_postMap` (which folds in `polyTime_postMapProg` + the tight-δ composition + the
    derived poly overhead), leaving ONLY the reduction's output-growth obligation `hout`
    (the one irreducibly-domain fact — a Lean `fun` has no runtime, so its declared work `cw`/`bw`
    and its output size are inputs, everything else is derived).

## Bars

PROOF-PRODUCING only: every tactic here is `simp` / `omega` / `refine` / `exact` against
kernel-clean lemmas. NO `native_decide`, NO `decide` on opaque props, NO `sorry`, NO `axiom`. A
tactic that cannot close its goal FAILS. `#assert_all_clean` at the bottom pins the datapoints
(both poles + the overhead nest) kernel-clean, so the automation cannot smuggle a non-kernel axiom
into a proof it drives.

The cost-is-syntactic rule is preserved: no tactic introduces an assertable cost field; `cost_simp`
only ever REWRITES `cost`/`stepCost` by their defining equations.
-/
import Dregg2.Crypto.CostAdversary
import Dregg2.Crypto.CostNormAttr
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Crypto.CostTactics

open Dregg2.Crypto.CostAdversary
open Dregg2.Crypto.FloorGames (Game Adversary)
open Dregg2.Crypto.ConcreteSecurity (PolyBoundedNat expBound expBound_not_ppt)

set_option autoImplicit false

/-! ## §1 — the `cost_norm` simp set: `Cost`-projection helpers.

The structural cost lemmas (`cost_pure`/`cost_tick`/`cost_query`/`cost_tickN`/`cost_reshape`/
`cost_probe`) and the `Cost`-projection lemmas already live in `CostAdversary` as `@[simp]`. We
join them into the `cost_norm` set below and add the few projection/`total` reductions the set
needs to bottom out at a concrete arithmetic expression. Each added lemma is `rfl`. -/

variable {O : Type}

/-- Projection of a literal cost vector: intrinsic component. -/
@[cost_norm] theorem Cost.mk_intr (a : ℕ) (q : O → ℕ) : (Cost.mk a q).intr = a := rfl

/-- Projection of a literal cost vector: query component. -/
@[cost_norm] theorem Cost.mk_qry (a : ℕ) (q : O → ℕ) (o : O) : (Cost.mk a q).qry o = q o := rfl

/-- The scalar of a literal cost vector — `total` unfolded on a `mk`. -/
@[cost_norm] theorem Cost.total_mk [Fintype O] (a : ℕ) (q : O → ℕ) :
    (Cost.mk a q).total = a + ∑ o, q o := rfl

-- The scalar distributes over the cost sum — so a cost built from `Cost.add` (as the structural
-- lemmas produce) has its `total` pushed to the leaves.
attribute [cost_norm] Cost.total_add

-- Join the existing structural + projection `@[simp]` lemmas into the `cost_norm` set. (They are
-- already `@[simp]`; this adds the `cost_norm` tag so `cost_simp`'s `simp only` sees them without
-- pulling in the entire global simp set.)
attribute [cost_norm]
  FreeOracle.cost_pure FreeOracle.cost_tick FreeOracle.cost_query
  FreeOracle.cost_tickN FreeOracle.cost_reshape FreeOracle.cost_probe
  Cost.zero_intr Cost.zero_qry Cost.add_intr Cost.add_qry
  Cost.tickC_intr Cost.tickC_qry Cost.callC_intr Cost.callC_qry
  Cost.supOver_intr Cost.supOver_qry
  LinCost.at'_intr LinCost.at'_qry
  Cost.billed_one

/-- **`cost_simp`** — reduce a `cost`/`stepCost` expression to concrete arithmetic, driven by the
`FreeOracle` program syntax. `cost_simp [extra]` adds unfolds for a game's own `sz`/adversary defs;
`cost_simp at h` / `cost_simp [extra] at h` rewrite a hypothesis. A REDUCTION, not an assertion:
it only rewrites `cost`/`stepCost`/`Cost.total`/`.intr`/`.qry` by their defining equations. -/
syntax "cost_simp" ("[" Lean.Parser.Tactic.simpLemma,* "]")? (Lean.Parser.Tactic.location)? :
  tactic

macro_rules
  | `(tactic| cost_simp [$lems,*] $[$loc:location]?) =>
    `(tactic| simp only [cost_norm, FreeOracle.stepCost, Cost.total, Cost.billed,
        Finset.univ_unique, Finset.sum_singleton, Finset.sum_const, Finset.card_univ,
        Finset.card_singleton, smul_eq_mul, Nat.add_zero, Nat.zero_add,
        Nat.mul_zero, Nat.zero_mul, Nat.mul_one, Nat.one_mul, $lems,*] $[$loc:location]?)
  | `(tactic| cost_simp $[$loc:location]?) =>
    `(tactic| simp only [cost_norm, FreeOracle.stepCost, Cost.total, Cost.billed,
        Finset.univ_unique, Finset.sum_singleton, Finset.sum_const, Finset.card_univ,
        Finset.card_singleton, smul_eq_mul, Nat.add_zero, Nat.zero_add,
        Nat.mul_zero, Nat.zero_mul, Nat.mul_one, Nat.one_mul] $[$loc:location]?)

/-! ## §2 — `poly_bound`: the `Nat`-polynomial closer (both poles). -/

/-- A monomial `C·lᵏ + C` is poly-bounded (the closure base case). -/
theorem polyBoundedNat_monomial (C k : ℕ) : PolyBoundedNat (fun l => C * l ^ k + C) :=
  ⟨k, C, fun _ => le_rfl⟩

/-- A bare power `lᵏ` is poly-bounded. -/
theorem polyBoundedNat_pow (k : ℕ) : PolyBoundedNat (fun l => l ^ k) :=
  ⟨k, 1, fun l => by rw [Nat.one_mul]; exact Nat.le_add_right _ _⟩

/-- The identity `l` is poly-bounded. -/
theorem polyBoundedNat_id : PolyBoundedNat (fun l => l) :=
  ⟨1, 1, fun l => by rw [pow_one, Nat.one_mul]; exact Nat.le_add_right _ _⟩

/-- **⚑ THE EXP POLE, AS A LEMMA.** A function that dominates `2^l` is NOT poly-bounded — the
engine of `bruteForce_not_polyTime`. Reduces the ⊤-collapse witness's `2^l ≤ e l` straight to
`expBound_not_ppt` (exp dominates poly, `ConcreteSecurity`), so the negative pole is one step. -/
theorem exp_dominates_not_poly {e : ℕ → ℕ} (hexp : ∀ l, 2 ^ l ≤ e l)
    (hpb : PolyBoundedNat e) : False :=
  expBound_not_ppt (polyBoundedNat_mono hexp hpb)

/-- **`poly_bound`** — discharge `PolyBoundedNat e` (or `∃ C k, ∀ l …, e ≤ C·lᵏ + C`) for a
concrete poly `e`, by recursing through the closure lemmas with monomial/constant leaves. It FAILS
on a non-poly shape (e.g. `2^l`, handled by the negative pole via `exp_dominates_not_poly`), never
fabricates. -/
syntax "poly_bound" : tactic

macro_rules
  | `(tactic| poly_bound) =>
    `(tactic| first
      | exact polyBoundedNat_const _
      | exact polyBoundedNat_monomial _ _
      | exact polyBoundedNat_pow _
      | exact polyBoundedNat_id
      | (refine polyBoundedNat_add ?_ ?_ <;> poly_bound)
      | (refine polyBoundedNat_const_mul _ ?_ <;> poly_bound)
      | (refine ⟨1, 1, ?_⟩ <;> intro l <;> (try intro i) <;>
          simp only [pow_one, Nat.one_mul, Nat.mul_one] <;> omega)
      | (refine ⟨1, 0, ?_⟩ <;> intro l <;> (try intro i) <;>
          simp only [pow_zero, Nat.mul_one, Nat.one_mul] <;> omega)
      | (refine ⟨2, 1, ?_⟩ <;> intro l <;> (try intro i) <;>
          simp only [pow_one] <;> nlinarith [Nat.zero_le l]))

/-! ## §3 — `poly_time`: efficiency preservation in one call. -/

/-- **The efficiency-preservation lemma, ARGUMENT-REORDERED for tactic use.** Identical content to
`isPolyTime_postMap`, but with the size measures `sz`/`sz'` FIRST so both games are concrete before
the equal-instance witness `fun _ => rfl` elaborates — otherwise that `rfl` collapses the two game
metavariables (`G' := G`) and the reshaper `f`'s codomain is misinferred. This is the reordering
the hand-proof achieved with explicit `(G := …) (G' := …)` annotations. -/
theorem isPolyTime_postMap' {G G' : Game}
    (sz : AnsSize G) (sz' : AnsSize G')
    (f : ∀ l, G.Inst l → G.Ans l → G'.Ans l)
    (hEq : ∀ l, G'.Inst l = G.Inst l) (cw bw co bo : ℕ)
    (hout : ∀ l (i : G.Inst l) (a : G.Ans l), sz' l (f l i a) ≤ co * sz l a + bo)
    {A : Adversary G} (hA : IsPolyTime sz A) :
    IsPolyTime sz' (Adversary.postMap hEq f A) :=
  isPolyTime_postMap hEq f sz sz' cw bw co bo hout hA

/-- **`poly_time sz sz' f cw bw co bo hA`** — prove `IsPolyTime sz' (Adversary.postMap (fun _ => rfl)
f A)` from `hA : IsPolyTime sz A`, where the reduction `f` is a pure output reshaping (tag passed
through) with declared work `cw·(input size) + bw`, whose output size grows by `co·(input) + bo`.
Applies `isPolyTime_postMap` (via the reordered `isPolyTime_postMap'`) — which folds in
`polyTime_postMapProg`, the tight-δ composition, and the DERIVED poly overhead — leaving ONLY the
output-growth obligation `hout` as a goal (proved from the game's own length facts). One call
replaces the game-annotation + size + poly boilerplate; `sz`/`sz'` pin the two games. -/
macro "poly_time" sz:term:max sz':term:max f:term:max
    cw:term:max bw:term:max co:term:max bo:term:max hA:term:max : tactic =>
  `(tactic| refine isPolyTime_postMap' $sz $sz' $f (fun _ => rfl) $cw $bw $co $bo ?_ $hA)

/-! ## §4 — LEVERAGE: the datapoints, at EQUAL strength, kernel-clean.

Each theorem below RE-PROVES a hand-written obligation of `CostAdversary` using the tactics, at the
same (or a defeq) statement, to MEASURE the collapse. The `#assert_all_clean` at the end pins them
to the kernel triple, so the automation is sound-by-construction. -/

open FreeOracle

/-- **⚑ THE ⊤ POLE via the tactics** (cf. `bruteForce_not_polyTime`, ~5 hand-lines → 3).
`cost_simp` reduces the enumerator's cost to `2^l + l`; `exp_dominates_not_poly` refutes the poly
bound. Equal strength: same statement. -/
theorem bruteForce_not_polyTime_tac : ¬ PolyTime expSize bruteForce := by
  rintro ⟨C, k, h⟩
  refine exp_dominates_not_poly (e := fun l => C * l ^ k + C) ?_ ⟨k, C, fun _ => le_rfl⟩
  intro l
  have hl := h l ()
  cost_simp [bruteForce, expSize, expWinner] at hl
  show 2 ^ l ≤ C * l ^ k + C
  omega

/-- **⚑ THE ⊥ POLE via the tactics** (cf. `idAdv_polyTime_expGame`). `poly_bound` supplies the
size witness `l ≤ 1·l¹ + 1`. Equal strength: same statement. -/
theorem idAdv_polyTime_expGame_tac :
    PolyTime expSize (idAdv (O := Unit) (Q := fun _ => Unit) (R := fun _ => Unit)
      (fun l _ => expWinner l)) :=
  idAdv_polyTime expSize _ (by simp only [expSize]; poly_bound)

/-- **⚑ THE OVERHEAD-POLY NEST via `poly_bound`** — the exact `PolyBoundedNat` obligation inside
`polyTime_postMapProg`'s proof (~6 hand-lines of nested `polyBoundedNat_add`/`_const_mul` → one
`poly_bound`). This is the arithmetic core of §3's efficiency-preservation; the tactic reproduces
it. -/
theorem overhead_poly_tac {P : Type} [Fintype P] (C k : ℕ) (slope base : ℕ) (qadd : P → ℕ) :
    PolyBoundedNat (fun l =>
      (C * l ^ k + C) + (slope * (C * l ^ k + C) + base + ∑ o, qadd o)) := by
  poly_bound

/-- The intrinsic half is poly too, from the same closer (cf. `queryHog_polyIntr`'s shape). -/
theorem monomial_sum_poly (C k C' k' : ℕ) :
    PolyBoundedNat (fun l => (C * l ^ k + C) + (C' * l ^ k' + C')) := by
  poly_bound

#assert_all_clean [
  bruteForce_not_polyTime_tac,
  idAdv_polyTime_expGame_tac,
  overhead_poly_tac,
  monomial_sum_poly,
  exp_dominates_not_poly,
  polyBoundedNat_monomial,
  polyBoundedNat_pow,
  polyBoundedNat_id
]

end Dregg2.Crypto.CostTactics
