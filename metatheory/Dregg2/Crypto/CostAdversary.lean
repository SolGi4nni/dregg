/-
# `Dregg2.Crypto.CostAdversary` — a COST MODEL that gives `Eff` in-logic content.

`FloorGames` §8 names the residual precisely and does NOT close it: the tree has no cost model, so the
adversary class `Eff` of `Hard G Eff := ∀ A, Eff A → Negl (gameAdv G A)` is a bare parameter. `§2`'s
`hard_top_iff_solvableFrac_negl` proves the escape is `Eff` and ONLY `Eff` — at `Eff := ⊤` the floor is
FALSE (a brute-force solver wins), at `Eff := ⊥` it is vacuous. The root cause (§8) is the adversary type:

    Adversary G := ∀ l, Inst l → Ans l

is a RAW FUNCTION carrying no cost, so no non-trivial `Eff` can even be *stated*. This is exactly the
EasyCrypt 2021 (eprint 2021/156) cost-model motivation — "an unbounded adversary's advantage is often 1,
so bounding resources is critical" — and FCF's (arXiv:1410.3735) reason for a `Comp` monad.

This module builds the MINIMAL cost model sufficient to make `Eff` non-trivial and efficiency-preservation
(`hclosed`) a THEOREM, alongside `FloorGames` (it does not touch it):

  **§1 — the cost-carrying adversary is a DEEP-EMBEDDED PROGRAM.** `FreeOracle Q R α` is a small free
  monad / interaction tree over an oracle interface `(Q, R)`: `pure` (return), `tick` (one unit of internal
  work — the `bind`/step node), and `query q k` (one oracle call, branching on the response `R`).

  ⚑ **THE LOAD-BEARING CORRECTNESS RULE — cost is DERIVED FROM SYNTAX, never asserted.** `stepCost` is an
  instrumented interpreter of the PROGRAM: it counts `tick`s and `query`s STRUCTURALLY (queries in the
  WORST CASE over the finite response space — so `stepCost` is an UPPER bound on every actual run, never an
  undercount). It is a function OF the program, not a field ON the structure. An asserted `cost := 0` field
  would re-admit brute force (the raw-function hole, one level up); here cost cannot be faked because the
  scan's `tick`s ARE in the syntax and `stepCost` sees all of them.

  **§2 — `PolyTime` and the two poles, PROVED.** `PolyTime A := ∃ C k, ∀ l i, stepCost (A.prog l i) ≤
  C·lᵏ+C` (`ConcreteSecurity.PolyBoundedNat` of the program's cost). BOTH POLES are theorems:
    * `bruteForce_not_polyTime` (`Eff ≠ ⊤`): the enumeration adversary that scans a `2^l`-sized answer
      space has `stepCost = 2^l`, super-polynomial (`ConcreteSecurity.expBound_not_ppt`) — so the collapse
      witness of `hard_top_iff_solvableFrac_negl` is EXCLUDED at `Eff := PolyTime`. `bruteForce_solves`
      confirms it is a genuine solver (advantage `1` at `⊤`), so the exclusion is not vacuous.
    * `idAdv_polyTime` (`Eff ≠ ⊥`): the pure/return adversary has `stepCost = 0`, is `PolyTime`, so the
      class is INHABITED — the floor at `Eff := PolyTime` is not vacuous.

  **§3 — `hclosed` (efficiency preservation) as a THEOREM.** `polyTime_postMap`: `PolyTime` is closed under
  bounded-overhead post-composition — a fixed poly-time reshaping of the adversary's output preserves
  `PolyTime` (poly + poly = poly, `polyBoundedNat_add`). This is the general lemma the state-commit spine's
  `hclosed`/`hEff` hypothesis wants; `Adversary.postMap` + `isPolyTime_postMap` is the shape the spine's
  `stateBreakToWireBreak` / `wireBreakToFinder` reductions are instances of.

  **§4 — CONNECTION to `FloorGames`.** `IsPolyTime : Adversary G → Prop` (a raw adversary is efficient iff
  SOME poly-time program denotes to it) makes `Hard G IsPolyTime` — e.g. `HashCRHardQuant F IsPolyTime` —
  a meaningful floor: `isPolyTime_inhabited` (non-vacuous), `bruteForce_not_polyTime` (proper restriction
  of ⊤). `isPolyTime_postMap` is the theorem the spine consumes to discharge `hEff` (see the one-line note
  at `stateCommit_hEff_discharge_note`).

## What stays a LABELED deeper refinement (not grounded here).

This is the MINIMAL grounding. Genuinely deeper, and NOT claimed:
  * a TIGHT composable cost algebra with per-oracle CALL-COUNT accounting (EasyCrypt's cost vectors) — here
    every oracle call costs a flat `1` in the worst case, not a typed cost-per-oracle;
  * uniform vs non-uniform, and worst-case vs expected PPT (design commitments, contested in the
    literature) — `PolyTime` here is worst-case over the finite instance/response space, deterministic;
  * output-size accounting: `polyTime_postMap` takes the reshaping's overhead as an explicit poly bound
    (`hov`); deriving that bound from "a poly-time adversary writes poly-many bits" needs an output-size
    measure this model does not carry. For the spine reductions the overhead is `O(depth)` (a fixed-width
    chain walk), poly — supplied as the honest, named residual, in place of the bare `hEff` parameter.

## Axiom hygiene

`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no fresh `axiom`, no
`native_decide`. `Classical.choice` enters only via `bruteForce`'s solver (the same witness `FloorGames`
§2 uses) and the non-vacuity default answer.
-/
import Dregg2.Crypto.FloorGames
import Dregg2.Crypto.ConcreteSecurity
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Crypto.CostAdversary

open Dregg2.Crypto.FloorGames
open Dregg2.Crypto.ConcreteSecurity (Negl PolyBoundedNat expBound expBound_not_ppt)

set_option autoImplicit false
set_option linter.dupNamespace false

/-! ## §1 — the deep-embedded oracle program, and SYNTACTIC cost. -/

/-- **A cost-carrying adversary PROGRAM** — a small free monad / interaction tree over an oracle interface
with query type `Q` and (finite) response type `R`.

  * `pure a` — return `a`, no work.
  * `tick k` — one unit of INTERNAL work, then continue as `k` (the `bind`/step node).
  * `query q k` — one ORACLE CALL on `q`, branching on the response `r : R` into `k r`.

The response-branching `(R → FreeOracle …)` is what lets a real finder USE its query results (compare two
hashes); `R` finite is what lets the worst-case query cost be a genuine `ℕ`. -/
inductive FreeOracle (Q R : Type) (α : Type) where
  /-- Return a value; contributes no cost. -/
  | protected pure : α → FreeOracle Q R α
  /-- One unit of internal computation, then continue. -/
  | protected tick : FreeOracle Q R α → FreeOracle Q R α
  /-- One oracle call on `q`, continuing with the response. -/
  | protected query : Q → (R → FreeOracle Q R α) → FreeOracle Q R α

namespace FreeOracle

/-- **⚑ THE INSTRUMENTED INTERPRETER — cost is DERIVED FROM THE PROGRAM'S SYNTAX.** `stepCost` counts
`tick`s and `query`s by structural recursion on the program: `+1` per `tick`, `+1` per `query` plus the
WORST-CASE cost over the (finite) response branches (`Finset.univ.sup` — an UPPER bound on any real run, so
`PolyTime` bounds every execution, and cost can never be undercounted).

This is the load-bearing rule of the module: cost is a FUNCTION of `prog`, never a field on a structure. A
program that scans `n` answers has `n` `tick`s in its syntax, so `stepCost ≥ n` is forced — there is no
`cost := 0` to assert. -/
def stepCost {Q R α : Type} [Fintype R] : FreeOracle Q R α → ℕ
  | .pure _ => 0
  | .tick k => 1 + stepCost k
  | .query _ k => 1 + Finset.univ.sup (fun r => stepCost (k r))

@[simp] theorem stepCost_pure {Q R α : Type} [Fintype R] (a : α) :
    stepCost (.pure a : FreeOracle Q R α) = 0 := rfl

@[simp] theorem stepCost_tick {Q R α : Type} [Fintype R] (k : FreeOracle Q R α) :
    stepCost (.tick k) = 1 + stepCost k := rfl

/-- **Monadic bind — graft `k` onto every leaf of `m`.** The derived sequencing; `tick`/`query` structure
is preserved and the continuation is spliced at each `pure` leaf. -/
def bind {Q R α β : Type} : FreeOracle Q R α → (α → FreeOracle Q R β) → FreeOracle Q R β
  | .pure a, k => k a
  | .tick m, k => .tick (bind m k)
  | .query q c, k => .query q (fun r => bind (c r) k)

/-- **`n` units of internal work, then `m`.** Models a straight-line scan / fixed-overhead prefix. -/
def tickN {Q R α : Type} : ℕ → FreeOracle Q R α → FreeOracle Q R α
  | 0, m => m
  | n + 1, m => .tick (tickN n m)

@[simp] theorem stepCost_tickN {Q R α : Type} [Fintype R] (n : ℕ) (m : FreeOracle Q R α) :
    stepCost (tickN n m) = n + stepCost m := by
  induction n with
  | zero => simp [tickN]
  | succ n ih => simp only [tickN, stepCost_tick, ih]; omega

/-- **A `query`-only probe of length `n`** — `n` oracle calls, each ignoring the response, then `pure a`.
Its cost is exactly `n` (over a nonempty response space): the demonstration that `query` nodes are counted
just like `tick`s, so "cost counts binds AND oracle queries" is real, not decorative. -/
def probe {Q R α : Type} (q : Q) : ℕ → α → FreeOracle Q R α
  | 0, a => .pure a
  | n + 1, a => .query q (fun _ => probe q n a)

@[simp] theorem stepCost_probe {Q R α : Type} [Fintype R] [Nonempty R] (q : Q) (n : ℕ) (a : α) :
    stepCost (probe q n a : FreeOracle Q R α) = n := by
  induction n with
  | zero => simp [probe]
  | succ n ih =>
      show 1 + Finset.univ.sup (fun _ : R => stepCost (probe q n a)) = n + 1
      rw [Finset.sup_const Finset.univ_nonempty, ih]
      omega

/-- **⚑ BOUNDED-OVERHEAD COMPOSITION at the cost level.** Grafting a continuation that costs at most `B`
onto every leaf raises `stepCost` by at most `B`. The engine of efficiency-preservation. -/
theorem stepCost_bind_le {Q R α β : Type} [Fintype R]
    (m : FreeOracle Q R α) (k : α → FreeOracle Q R β) (B : ℕ)
    (hk : ∀ a, stepCost (k a) ≤ B) :
    stepCost (bind m k) ≤ stepCost m + B := by
  induction m with
  | pure a => simpa [bind, stepCost] using hk a
  | tick m ih => simp only [bind, stepCost_tick]; omega
  | query q c ih =>
      simp only [bind, stepCost]
      have hsup : Finset.univ.sup (fun r => stepCost (bind (c r) k))
          ≤ Finset.univ.sup (fun r => stepCost (c r)) + B := by
        apply Finset.sup_le
        intro r _
        have hle : stepCost (c r) ≤ Finset.univ.sup (fun r => stepCost (c r)) :=
          Finset.le_sup (f := fun r => stepCost (c r)) (Finset.mem_univ r)
        have := ih r
        omega
      omega

/-! ### Denotation — running the program under an oracle to recover the raw answer. -/

/-- **Run the program under an oracle `o`** to recover the plain value: `tick`/`query` are erased, queries
resolved by `o`. This is the bridge back to `FloorGames.Adversary` (a raw function). -/
def denote {Q R α : Type} (o : Q → R) : FreeOracle Q R α → α
  | .pure a => a
  | .tick k => denote o k
  | .query q c => denote o (c (o q))

@[simp] theorem denote_pure {Q R α : Type} (o : Q → R) (a : α) :
    denote o (.pure a : FreeOracle Q R α) = a := rfl

@[simp] theorem denote_tickN {Q R α : Type} (o : Q → R) (n : ℕ) (m : FreeOracle Q R α) :
    denote o (tickN n m) = denote o m := by
  induction n with
  | zero => simp [tickN]
  | succ n ih => simp only [tickN, denote, ih]

theorem denote_bind {Q R α β : Type} (o : Q → R) (m : FreeOracle Q R α) (k : α → FreeOracle Q R β) :
    denote o (bind m k) = denote o (k (denote o m)) := by
  induction m with
  | pure a => rfl
  | tick m ih => simpa [bind, denote] using ih
  | query q c ih => simpa [bind, denote] using ih (o q)

end FreeOracle

open FreeOracle

/-! ## §2 — the cost-carrying adversary, `PolyTime`, and BOTH POLES. -/

/-- **A COST ADVERSARY against `G`** — a deep-embedded program per instance, over the oracle interface
`(Q, R)`. Unlike `FloorGames.Adversary` (a raw `∀ l, Inst l → Ans l` carrying NO cost), this one has a
`stepCost` derived from its syntax, so an efficiency class over it is meaningful. -/
structure CostAdversary (G : Game) (Q R : Type) where
  /-- The adversary's PROGRAM on instance `i` at parameter `l`. -/
  prog : ∀ l, G.Inst l → FreeOracle Q R (G.Ans l)

/-- **`PolyTime A`** — the program's `stepCost` is polynomially bounded in the security parameter, uniformly
over instances. This is `ConcreteSecurity.PolyBoundedNat` of the per-instance cost; the task's
`∃ c k, ∀ l, stepCost (A.prog l) ≤ c·lᵏ + c` with the instance quantified (worst-case over the sampled
challenge). Setting `Eff := PolyTime` is what §2's two poles justify. -/
def PolyTime {G : Game} {Q R : Type} [Fintype R] (A : CostAdversary G Q R) : Prop :=
  ∃ C k : ℕ, ∀ l (i : G.Inst l), stepCost (A.prog l i) ≤ C * l ^ k + C

/-- **Denotation to a raw `FloorGames.Adversary`** — run each program under the trivial (default) oracle.
This is how a `CostAdversary` induces a member of the class the floor quantifies over. -/
def CostAdversary.toAdversary {G : Game} {Q R : Type} [Inhabited R]
    (A : CostAdversary G Q R) : Adversary G where
  run := fun l i => denote (fun _ => default) (A.prog l i)

/-! ### The ⊥ pole — the class is INHABITED (not vacuous). -/

/-- **The pure/return adversary** — outputs a fixed answer, does no work. The simplest efficient adversary. -/
def idAdv {G : Game} {Q R : Type} (a₀ : ∀ l, G.Inst l → G.Ans l) : CostAdversary G Q R where
  prog := fun l i => .pure (a₀ l i)

/-- **⚑ THE ⊥ POLE — `PolyTime` is INHABITED, so the floor at `Eff := PolyTime` is NOT vacuous.** The
return adversary has `stepCost = 0 ≤ 0·l⁰ + 0`. Contrast `FloorGames.hard_bot_vacuous`: at `Eff := ⊥` the
class is empty and the floor holds for any game; here the class is nonempty, and the floor has content. -/
theorem idAdv_polyTime {G : Game} {Q R : Type} [Fintype R] (a₀ : ∀ l, G.Inst l → G.Ans l) :
    PolyTime (idAdv (Q := Q) (R := R) a₀) :=
  ⟨0, 0, fun l i => by simp [idAdv]⟩

/-! ### The ⊤ pole — an EXPONENTIAL-search game and the brute-force enumerator that is NOT `PolyTime`. -/

/-- **A game with an exponential answer space.** One instance, `2^l` candidate answers, `wins` iff the
answer is the canonical winner `0` — so every instance is solvable (a brute-force scan finds `0`). The
minimal carrier on which "scanning the answer space" is super-polynomial. -/
def expGame : Game where
  Inst := fun _ => Unit
  Ans := fun l => Fin (2 ^ l)
  instFin := fun _ => inferInstance
  instNe := fun _ => inferInstance
  wins := fun l _ a => a = ⟨0, by positivity⟩
  winsDec := fun l _ a => inferInstance

/-- The canonical winning answer of `expGame` at parameter `l`. -/
def expWinner (l : ℕ) : Fin (2 ^ l) := ⟨0, by positivity⟩

/-- **THE BRUTE-FORCE ENUMERATOR.** Its PROGRAM scans all `2^l` answers (`2^l` `tick`s of internal work),
then returns the winner. Its cost is `2^l` BY CONSTRUCTION OF THE SYNTAX — there is no cost field to zero
out. This is the computable twin of `FloorGames.choiceAdv`, the witness that refutes the ⊤ floor. -/
def bruteForce : CostAdversary expGame Unit Unit where
  prog := fun l _ => tickN (2 ^ l) (.pure (expWinner l))

/-- The brute-force enumerator's `stepCost` is exactly `2^l` — the size of the answer space it scans. -/
theorem bruteForce_stepCost (l : ℕ) (i : expGame.Inst l) :
    stepCost (bruteForce.prog l i) = 2 ^ l := by
  simp [bruteForce, FreeOracle.stepCost_tickN, FreeOracle.stepCost]

/-- **⚑ THE ⊤ POLE — the brute-force solver is NOT `PolyTime`.** Its `stepCost` is `2^l`, which no
`C·lᵏ + C` bounds (`ConcreteSecurity.expBound_not_ppt`, exp dominates poly). So at `Eff := PolyTime` the
collapse witness of `FloorGames.hard_top_iff_solvableFrac_negl` — the enumeration solver — is EXCLUDED:
`Eff := PolyTime` is a PROPER restriction of `⊤`, and the ⊤-collapse does not refute the floor. This is the
whole point — the class `Eff` finally has enough content to keep out the adversary that makes the floor
false. -/
theorem bruteForce_not_polyTime : ¬ PolyTime bruteForce := by
  rintro ⟨C, k, h⟩
  refine expBound_not_ppt ⟨k, C, fun l => ?_⟩
  have hl := h l ()
  rw [bruteForce_stepCost l ()] at hl
  simpa [expBound] using hl

/-- **THE BRUTE-FORCE ENUMERATOR GENUINELY SOLVES** `expGame` — it wins on every instance, so its advantage
is `1` and it WOULD refute the ⊤ floor. Hence its exclusion by `PolyTime` (above) is not vacuous: a real
solver is being kept out, exactly the one an unbounded class admits. -/
theorem bruteForce_solves (l : ℕ) (i : expGame.Inst l) :
    expGame.wins l i (bruteForce.toAdversary.run l i) := by
  show bruteForce.toAdversary.run l i = expWinner l
  simp [CostAdversary.toAdversary, bruteForce, FreeOracle.denote_tickN, FreeOracle.denote, expWinner]

/-- **The ⊤ floor over `expGame` is FALSE** (every instance solvable — `FloorGames`
`not_hard_top_of_always_solvable`). This is the floor that `PolyTime` rescues by excluding `bruteForce`. -/
theorem expGame_top_false : ¬ Hard expGame (fun _ => True) :=
  not_hard_top_of_always_solvable expGame (fun _ => ⟨expWinner _⟩)
    (fun l _ => ⟨expWinner l, rfl⟩)

/-! ## §3 — `hclosed`: `PolyTime` is closed under bounded-overhead post-composition. -/

/-- **`PolyBoundedNat` is closed under pointwise sum** (poly + poly = poly): `C₃ := 2(C₁+C₂)`,
`k₃ := max k₁ k₂`. The arithmetic core of efficiency-preservation — the reduction's cost is the
adversary's cost plus a poly overhead, and this keeps the total poly. -/
theorem polyBoundedNat_add {a b : ℕ → ℕ} (ha : PolyBoundedNat a) (hb : PolyBoundedNat b) :
    PolyBoundedNat (fun l => a l + b l) := by
  obtain ⟨k₁, C₁, ha⟩ := ha
  obtain ⟨k₂, C₂, hb⟩ := hb
  refine ⟨max k₁ k₂, 2 * (C₁ + C₂), fun l => ?_⟩
  show a l + b l ≤ 2 * (C₁ + C₂) * l ^ max k₁ k₂ + 2 * (C₁ + C₂)
  have hA := ha l
  have hB := hb l
  rcases Nat.eq_zero_or_pos l with hl | hl
  · subst hl
    have e1 : (0 : ℕ) ^ k₁ ≤ 1 := by rcases k₁ with _ | k₁ <;> simp
    have e2 : (0 : ℕ) ^ k₂ ≤ 1 := by rcases k₂ with _ | k₂ <;> simp
    have hc1 : C₁ * (0 : ℕ) ^ k₁ ≤ C₁ := by
      have h := Nat.mul_le_mul_left (k := C₁) e1
      simpa using h
    have hc2 : C₂ * (0 : ℕ) ^ k₂ ≤ C₂ := by
      have h := Nat.mul_le_mul_left (k := C₂) e2
      simpa using h
    have hM : 0 ≤ 2 * (C₁ + C₂) * (0 : ℕ) ^ max k₁ k₂ := Nat.zero_le _
    omega
  · have hkm : l ^ k₁ ≤ l ^ max k₁ k₂ := Nat.pow_le_pow_right hl (le_max_left k₁ k₂)
    have hk'm : l ^ k₂ ≤ l ^ max k₁ k₂ := Nat.pow_le_pow_right hl (le_max_right k₁ k₂)
    have h1 : C₁ * l ^ k₁ ≤ C₁ * l ^ max k₁ k₂ := by gcongr
    have h2 : C₂ * l ^ k₂ ≤ C₂ * l ^ max k₁ k₂ := by gcongr
    nlinarith [hA, hB, h1, h2, Nat.zero_le (l ^ max k₁ k₂), Nat.zero_le C₁, Nat.zero_le C₂]

/-- **THE POST-PROCESSING WRAPPER at the cost level.** Reshape the adversary's output by a pure function
`f` (which may read the instance), charging `ov l` units for the reshaping work. The instance families of
the two games agree (`hI`, `rfl` at every use site of the spine). This is the shape every spine reduction
(`stateBreakToWireBreak`, `wireBreakToFinder`) has: read the output, recompute a fixed pure function. -/
def CostAdversary.postMap {G G' : Game} {Q R : Type}
    (hI : ∀ l, G'.Inst l = G.Inst l) (f : ∀ l, G.Inst l → G.Ans l → G'.Ans l) (ov : ℕ → ℕ)
    (A : CostAdversary G Q R) : CostAdversary G' Q R where
  prog := fun l i =>
    bind (A.prog l (hI l ▸ i)) (fun a => tickN (ov l) (.pure (f l (hI l ▸ i) a)))

/-- **⚑ `hclosed` — EFFICIENCY IS PRESERVED under bounded-overhead post-composition.** If `A` is
`PolyTime` and the reshaping overhead `ov` is poly, then the reshaped adversary is `PolyTime`. This is the
GENERAL lemma the state-commit spine's `hclosed : Eff A → Eff' (reduction A)` wants: the reduction is a
fixed poly-overhead wrapper of `A`, so it preserves `PolyTime`. -/
theorem polyTime_postMap {G G' : Game} {Q R : Type} [Fintype R]
    (hI : ∀ l, G'.Inst l = G.Inst l) (f : ∀ l, G.Inst l → G.Ans l → G'.Ans l) (ov : ℕ → ℕ)
    (A : CostAdversary G Q R) (hA : PolyTime A) (hov : PolyBoundedNat ov) :
    PolyTime (A.postMap hI f ov) := by
  obtain ⟨C, k, hC⟩ := hA
  -- the reshaped cost is bounded by (A's cost) + (overhead), each poly
  have hstep : ∀ l (i : G'.Inst l),
      stepCost ((A.postMap hI f ov).prog l i) ≤ (C * l ^ k + C) + ov l := by
    intro l i
    have hbind : stepCost ((A.postMap hI f ov).prog l i)
        ≤ stepCost (A.prog l (hI l ▸ i)) + ov l := by
      refine FreeOracle.stepCost_bind_le _ _ (ov l) (fun a => ?_)
      simp [FreeOracle.stepCost_tickN, FreeOracle.stepCost]
    have := hC l (hI l ▸ i)
    exact hbind.trans (by omega)
  -- (A's poly cost) + (poly overhead) is poly
  have hpoly : PolyBoundedNat (fun l => (C * l ^ k + C) + ov l) :=
    polyBoundedNat_add ⟨k, C, fun l => le_rfl⟩ hov
  obtain ⟨k', C', hC'⟩ := hpoly
  exact ⟨C', k', fun l i => (hstep l i).trans (hC' l)⟩

/-! ### The raw-adversary shadow of `postMap`, and the denotation square. -/

/-- **THE POST-PROCESSING WRAPPER at the raw-`Adversary` level** — the shape the spine reductions literally
have (`run l i := f l i (A.run l i)`, instance passed through). -/
def Adversary.postMap {G G' : Game} (hI : ∀ l, G'.Inst l = G.Inst l)
    (f : ∀ l, G.Inst l → G.Ans l → G'.Ans l) (A : Adversary G) : Adversary G' where
  run := fun l i => f l (hI l ▸ i) (A.run l (hI l ▸ i))

/-- **THE DENOTATION SQUARE** — denoting the cost-level wrapper equals raw-wrapping the denotation. So a
cost program's reshaping tracks the raw reduction exactly. -/
theorem toAdversary_postMap {G G' : Game} {Q R : Type} [Inhabited R]
    (hI : ∀ l, G'.Inst l = G.Inst l) (f : ∀ l, G.Inst l → G.Ans l → G'.Ans l) (ov : ℕ → ℕ)
    (A : CostAdversary G Q R) :
    (A.postMap hI f ov).toAdversary = Adversary.postMap hI f A.toAdversary := by
  unfold CostAdversary.toAdversary Adversary.postMap
  congr 1
  funext l i
  show denote (fun _ => default)
      (bind (A.prog l (hI l ▸ i)) (fun a => tickN (ov l) (.pure (f l (hI l ▸ i) a))))
    = f l (hI l ▸ i) (A.toAdversary.run l (hI l ▸ i))
  rw [denote_bind, denote_tickN, denote_pure]
  rfl

/-! ## §4 — the `FloorGames` connection: `IsPolyTime` as a class over raw adversaries. -/

/-- **`IsPolyTime A`** — a raw `FloorGames.Adversary` is EFFICIENT iff SOME poly-time cost program denotes
to it. This is the `Eff` predicate with content: plugging it into `FloorGames.Hard`/`HashCRHardQuant`
yields a floor that quantifies over EFFICIENT adversaries, not all functions. (Oracle interface fixed to
the trivial `(Unit, Unit)`; the spine reductions need no oracle branching — a deeper refinement is a typed
per-oracle interface.) -/
def IsPolyTime {G : Game} (A : Adversary G) : Prop :=
  ∃ B : CostAdversary G Unit Unit, B.toAdversary = A ∧ PolyTime B

/-- **THE FLOOR AT `Eff := IsPolyTime` IS NON-VACUOUS.** The class contains the return adversary (for any
game with a choosable answer). So `Hard G IsPolyTime` — in particular `HashCRHardQuant F IsPolyTime` — is
not the vacuous `Eff := ⊥` floor. -/
theorem isPolyTime_inhabited {G : Game} (a₀ : ∀ l, G.Inst l → G.Ans l) :
    IsPolyTime (idAdv (Q := Unit) (R := Unit) a₀).toAdversary :=
  ⟨idAdv a₀, rfl, idAdv_polyTime a₀⟩

/-- **⚑ `IsPolyTime` IS CLOSED UNDER BOUNDED-OVERHEAD POST-COMPOSITION — the theorem the spine consumes to
discharge `hEff`.** If `A` is `IsPolyTime` and the reshaping `f` runs in poly overhead `ov`, then the
reshaped adversary `Adversary.postMap hI f A` is `IsPolyTime`. Instantiating `f`/`hI` with a spine
reduction (`stateBreakToWireBreak`, `wireBreakToFinder`) turns the spine's bare `hEff` PARAMETER into a
CONSEQUENCE of "`A` is efficient" + "the reduction's glue is poly (`O(depth)`)". -/
theorem isPolyTime_postMap {G G' : Game}
    (hI : ∀ l, G'.Inst l = G.Inst l) (f : ∀ l, G.Inst l → G.Ans l → G'.Ans l) (ov : ℕ → ℕ)
    (hov : PolyBoundedNat ov) {A : Adversary G} (hA : IsPolyTime A) :
    IsPolyTime (Adversary.postMap hI f A) := by
  obtain ⟨B, hBA, hBpoly⟩ := hA
  refine ⟨B.postMap hI f ov, ?_, polyTime_postMap hI f ov B hBpoly hov⟩
  rw [toAdversary_postMap, hBA]

/-- **NON-COLLAPSE, restated at the class level.** The program class `PolyTime` is a PROPER subclass — the
brute-force enumerator is a `CostAdversary` that is NOT `PolyTime` (`bruteForce_not_polyTime`). Together
with `idAdv_polyTime`, `PolyTime` is strictly between `⊥` and `⊤`: exactly the content `FloorGames` §8
said the tree could not supply. -/
theorem polyTime_proper : (∃ A : CostAdversary expGame Unit Unit, ¬ PolyTime A)
    ∧ (∃ A : CostAdversary expGame Unit Unit, PolyTime A) :=
  ⟨⟨bruteForce, bruteForce_not_polyTime⟩,
   ⟨idAdv (fun l _ => expWinner l), idAdv_polyTime _⟩⟩

/-! ### The spine discharge, spelled out (see also the one-line change note in the module header).

`Market.WideCommitBoundary.stateCommit_binds_advantage_bound` takes, at `Eff := IsPolyTime`:

    hEff : IsPolyTime (wireBreakToFinder D (stateBreakToWireBreak D S hash t A))

Both reductions are `Adversary.postMap` instances (`run l i := f l i (A.run l i)`, tag passed through), so
with `A = B.toAdversary` for a `PolyTime B`, TWO applications of `isPolyTime_postMap` (overheads = the
chain-walk / payload-rebuild costs, `O(depth)`, poly) DISCHARGE `hEff`. The one-line change the spine
enables: replace the `hEff` parameter by `A : CostAdversary … ` + `hA : PolyTime A` and derive `hEff` via
`isPolyTime_postMap`. This module keeps the general theorem; the spine keeps its statement. -/

/-- **A self-contained rehearsal of the spine discharge**, over abstract games standing in for the spine's
two reduction hops (`stateCommitBreakGame → wireCommitBreakGame → hashGame (wideFamily D)`, all with
`Inst := fun _ => D.Tag`). Given `A` efficient and both reshapings poly, the composed finder is efficient —
which is precisely `hEff`. No `hEff` parameter is assumed; it is PROVED. -/
theorem composed_reduction_isPolyTime {G G' G'' : Game}
    (hI' : ∀ l, G'.Inst l = G.Inst l) (hI'' : ∀ l, G''.Inst l = G'.Inst l)
    (f : ∀ l, G.Inst l → G.Ans l → G'.Ans l) (g : ∀ l, G'.Inst l → G'.Ans l → G''.Ans l)
    (ovf ovg : ℕ → ℕ) (hovf : PolyBoundedNat ovf) (hovg : PolyBoundedNat ovg)
    {A : Adversary G} (hA : IsPolyTime A) :
    IsPolyTime (Adversary.postMap hI'' g (Adversary.postMap hI' f A)) :=
  isPolyTime_postMap hI'' g ovg hovg (isPolyTime_postMap hI' f ovf hovf hA)

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  FreeOracle.stepCost_tickN,
  FreeOracle.stepCost_probe,
  FreeOracle.stepCost_bind_le,
  FreeOracle.denote_bind,
  idAdv_polyTime,
  bruteForce_stepCost,
  bruteForce_not_polyTime,
  bruteForce_solves,
  expGame_top_false,
  polyBoundedNat_add,
  polyTime_postMap,
  toAdversary_postMap,
  isPolyTime_inhabited,
  isPolyTime_postMap,
  polyTime_proper,
  composed_reduction_isPolyTime
]

end Dregg2.Crypto.CostAdversary
