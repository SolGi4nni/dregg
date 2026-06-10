/-
# Dregg2.Proof.ForestLTS — the N-ary cross-cell forest LTS.

Builds the executable account-update forest transition
`forestApply : (ι → KernelState) → ForestTurn → Option (ι → KernelState)` over a `Fintype ι`
family of cells, its abstraction `forestAbsOf`, the N-ary joint-balance measure
`forestJointBalance` (`Finset.sum`-over-`univ`), and the N-ary abstract step `forestAbsStep`.
Closes the N-ary forward-simulation square `forestAbsStep_forward` with the CG-5 Σ=0 binding
(`Σ_{i∈univ} δ i = 0`) as an explicit HYPOTHESIS, never derived. The bilateral
`CrossCellLTS.crossAbsStep` is the `ι = Fin 2` slice (`forestAbsStep_two_refines_crossAbs`).

Read-only consumer of `Exec.JointCell`, `Exec.Kernel`, `Spec.ExecRefinement`, `Hyperedge`,
`Proof.CrossCellLTS`.
-/
import Dregg2.Exec.JointCell
import Dregg2.Spec.ExecRefinement
import Dregg2.Proof.CrossCellLTS
import Dregg2.Hyperedge
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Basic

namespace Dregg2.Proof.ForestLTS

open Dregg2.Exec
open Dregg2.Exec.JointCell
open Dregg2.Spec
open scoped BigOperators

universe v

/-! ## §1 — The executable N-ary forest transition.

A `ForestTurn` over a finite index `ι` is the account-update forest: one shared turn-id `sid`
(CG-2, the apex), and per-incidence data `actorA i`, `srcA i`, and a signed half-delta `δ i`
(cell `i`'s contribution to the cross-family flow; negative = debit, positive = credit).
Admissibility requires the half-deltas to sum to zero (CG-5); that Σ=0 fact is the binding
carried as an explicit hypothesis throughout. -/

/-- A **forest turn** over the index `ι`. Each incidence `i` names its `actorA i` (authoriser),
its source cell `srcA i`, and its signed half-edge `δ i` (cell `i`'s ledger total moves by
`−δ i`). One shared `sid` (CG-2, the apex of the wide pullback). -/
structure ForestTurn (ι : Type v) where
  /-- Per-incidence authoriser of cell `i`'s half. -/
  actorA : ι → CellId
  /-- Per-incidence source cell whose balance cell `i`'s half rewrites. -/
  srcA   : ι → CellId
  /-- Per-incidence SIGNED half-edge delta (cell `i`'s contribution to the cross-flow). -/
  δ      : ι → ℤ
  /-- The shared turn-id (CG-2 / `account_updates_hash`) all incidences commit to. -/
  sid    : SharedId

/-- Cell `i`'s half-edge — signed debit, fail-closed. Commits only when `actorA i` is authorised
over `srcA i` and `srcA i` is a live account; rewrites `srcA i` by `−δ i`. No `0 ≤ δ`
availability gate — a cell may be a net receiver (`δ i < 0`). The Σ=0 balance is the separate
CG-5 binding. -/
def applyForestHalf (k : KernelState) (actor src : CellId) (d : ℤ) : Option KernelState :=
  if authorizedB k.caps { actor := actor, src := src, dst := src, amt := d } = true
      ∧ src ∈ k.accounts then
    some { k with bal := fun c => if c = src then k.bal c - d else k.bal c }
  else
    none

/-- The executable N-ary forest transition, fail-closed and atomic: returns `some cells'` iff
every incidence's half commits (`applyForestHalf` succeeds for every `i`). -/
def forestApply {ι : Type v} [Fintype ι] [DecidableEq ι]
    (cells : ι → KernelState) (ft : ForestTurn ι) : Option (ι → KernelState) :=
  if h : ∀ i, (applyForestHalf (cells i) (ft.actorA i) (ft.srcA i) (ft.δ i)).isSome then
    some (fun i => (applyForestHalf (cells i) (ft.actorA i) (ft.srcA i) (ft.δ i)).get (h i))
  else
    none

/-! ## §2 — Per-half effects + extraction lemmas. -/

/-- A committed forest half preserves `caps` (rewrites only `bal`), so the authority graph is
unchanged. -/
theorem applyForestHalf_caps {k k' : KernelState} {actor src : CellId} {d : ℤ}
    (h : applyForestHalf k actor src d = some k') : k'.caps = k.caps := by
  unfold applyForestHalf at h
  by_cases hg : authorizedB k.caps { actor := actor, src := src, dst := src, amt := d } = true
      ∧ src ∈ k.accounts
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h; rfl
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- A committed forest half preserves the live account set. -/
theorem applyForestHalf_accounts {k k' : KernelState} {actor src : CellId} {d : ℤ}
    (h : applyForestHalf k actor src d = some k') : k'.accounts = k.accounts := by
  unfold applyForestHalf at h
  by_cases hg : authorizedB k.caps { actor := actor, src := src, dst := src, amt := d } = true
      ∧ src ∈ k.accounts
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h; rfl
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- A committed forest half passed its authority gate over `src`. -/
theorem applyForestHalf_authz {k k' : KernelState} {actor src : CellId} {d : ℤ}
    (h : applyForestHalf k actor src d = some k') :
    authorizedB k.caps { actor := actor, src := src, dst := src, amt := d } = true := by
  unfold applyForestHalf at h
  by_cases hg : authorizedB k.caps { actor := actor, src := src, dst := src, amt := d } = true
      ∧ src ∈ k.accounts
  · exact hg.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- A committed forest half moves its ledger's total by exactly `−d`. The per-cell summand of
the Σ-conservation telescoping. -/
theorem applyForestHalf_total {k k' : KernelState} {actor src : CellId} {d : ℤ}
    (h : applyForestHalf k actor src d = some k') : total k' = total k - d := by
  unfold applyForestHalf at h
  by_cases hg : authorizedB k.caps { actor := actor, src := src, dst := src, amt := d } = true
      ∧ src ∈ k.accounts
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, hsrc⟩ := hg
    show (∑ c ∈ k.accounts, (if c = src then k.bal c - d else k.bal c))
        = (∑ c ∈ k.accounts, k.bal c) - d
    have hg2 : ∀ c ∈ k.accounts,
        (if c = src then k.bal c - d else k.bal c)
          = k.bal c + (if c = src then (-d) else 0) := by
      intro c _
      rcases eq_or_ne c src with h1 | h1
      · subst h1; rw [if_pos rfl, if_pos rfl]; ring
      · rw [if_neg h1, if_neg h1]; ring
    rw [Finset.sum_congr rfl hg2, Finset.sum_add_distrib,
        sum_indicator k.accounts src (-d) hsrc]
    ring
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- If the forest transition commits, every incidence's half committed individually. Extracts
`applyForestHalf … = some (cells' i)` for every `i`. -/
theorem forestApply_atomic {ι : Type v} [Fintype ι] [DecidableEq ι]
    {cells cells' : ι → KernelState} {ft : ForestTurn ι}
    (h : forestApply cells ft = some cells') :
    ∀ i, applyForestHalf (cells i) (ft.actorA i) (ft.srcA i) (ft.δ i) = some (cells' i) := by
  unfold forestApply at h
  by_cases hall : ∀ i, (applyForestHalf (cells i) (ft.actorA i) (ft.srcA i) (ft.δ i)).isSome
  · rw [dif_pos hall] at h
    simp only [Option.some.injEq] at h
    intro i
    rw [← h]
    exact (Option.some_get (hall i)).symm
  · rw [dif_neg hall] at h; exact absurd h (by simp)

/-! ## §3 — The N-ary carrier, abstraction, and joint-balance measure.

The cross-family abstract state is the family `ι → AbstractState`. The conserved measure is the
`Finset.sum`-over-`univ` of per-cell `balanceTotal`s — the N-ary generalization of `jointBalance`
(= `Σ_{Fin 2}`). -/

/-- The N-ary cross-cell abstraction function: maps a family of ledgers to the family of their
single-cell abstractions. -/
def forestAbsOf {ι : Type v} (cells : ι → KernelState) : ι → AbstractState :=
  fun i => absOf (cells i)

/-- The N-ary cross-cell conserved measure: `Finset.sum`-over-`univ` of the per-cell
`balanceTotal`s. No proper sub-family total is preserved alone — only the joint sum is the
invariant (mirroring `cross_conservation_is_not_per_cell`). -/
def forestJointBalance {ι : Type v} [Fintype ι] (p : ι → AbstractState) : ℤ :=
  ∑ i, (p i).balanceTotal

/-- `forestJointBalance (forestAbsOf cells) = Σ_i total (cells i)` — definitional. -/
theorem forestJointBalance_forestAbsOf {ι : Type v} [Fintype ι] (cells : ι → KernelState) :
    forestJointBalance (forestAbsOf cells) = ∑ i, total (cells i) := rfl

/-! ## §4 — `forestAbsStep` — the N-ary cross-cell abstract LTS edge. -/

/-- **`forestAbsStep ft p p'`** — the N-ary cross-cell abstract LTS edge for forest turn `ft`:

  * (C5) the joint `forestJointBalance` is preserved (the Σ of half-deltas cancels by the binding;
    no per-cell total is fixed individually);
  * (A) `∀ i, (p' i).authGraph = (p i).authGraph` — a balance forest mutates no cap;
  * (G) `ft`'s incidence `i` is authorized in `p i`'s authority graph (ownership ∨ `Graph.has`). -/
def forestAbsStep {ι : Type v} [Fintype ι] (ft : ForestTurn ι) (p p' : ι → AbstractState) : Prop :=
  -- (C5) cross-family conservation: the JOINT family total is preserved.
  forestJointBalance p' = forestJointBalance p ∧
  -- (A) authority frame on every cell: a balance forest mutates no cap.
  (∀ i, (p' i).authGraph = (p i).authGraph) ∧
  -- (G) grounding on every cell: each half is authorized in its own authority graph.
  (∀ i, ft.actorA i = ft.srcA i ∨ (p i).authGraph.has (ft.actorA i) (ft.srcA i))

/-- The N-ary LTS edge with the forest turn existentially closed: `p ⟶ p'` iff some forest turn
realizes `forestAbsStep`. -/
def ForestAbsStep {ι : Type v} [Fintype ι] (p p' : ι → AbstractState) : Prop :=
  ∃ ft : ForestTurn ι, forestAbsStep ft p p'

/-! ## §5 — The Σ-conservation telescoping. -/

/-- **`forestApply_cg5_conserves`** — a committed forest transition preserves the joint family
total `Σ_i total (cells i)`, given the CG-5 Σ=0 binding `Σ_i δ i = 0` (an explicit HYPOTHESIS,
never derived). Telescoping: each half moves its total by `−δ i`, summing gives
`Σ total (cells' i) = Σ total (cells i) − Σ δ i`, and the binding kills the second sum.
The binding is load-bearing: without it the joint total need not be preserved. -/
theorem forestApply_cg5_conserves {ι : Type v} [Fintype ι] [DecidableEq ι]
    {cells cells' : ι → KernelState} {ft : ForestTurn ι}
    (hbind : ∑ i, ft.δ i = 0)
    (h : forestApply cells ft = some cells') :
    ∑ i, total (cells' i) = ∑ i, total (cells i) := by
  have hhalf := forestApply_atomic h
  -- per-cell: `total (cells' i) = total (cells i) − δ i`.
  have hcell : ∀ i, total (cells' i) = total (cells i) - ft.δ i :=
    fun i => applyForestHalf_total (hhalf i)
  calc ∑ i, total (cells' i)
      = ∑ i, (total (cells i) - ft.δ i) := by
        exact Finset.sum_congr rfl (fun i _ => hcell i)
    _ = (∑ i, total (cells i)) - (∑ i, ft.δ i) := by rw [Finset.sum_sub_distrib]
    _ = (∑ i, total (cells i)) - 0 := by rw [hbind]
    _ = ∑ i, total (cells i) := by ring

/-! ## §6 — The N-ary cross-cell forward-simulation square.

```
                forestAbsOf
   cells ───────────────────────▶  (fun i => absOf (cells i))
     │                                   │
     │ forestApply cells ft = cells'      │ forestAbsStep ft
     ▼                                   ▼
   cells' ─────────────────────▶  (fun i => absOf (cells' i))
                forestAbsOf
```

Every committed `forestApply` step, under the CG-5 Σ=0 binding, is matched by `forestAbsStep ft`. -/

/-- **KEYSTONE — `forestAbsStep_forward`.** The N-ary cross-cell forward-simulation square: every
committed forest turn, given `Σ_i δ i = 0` (explicit HYPOTHESIS, never derived), is matched by
`forestAbsStep ft`. Assembles (C5) from `forestApply_cg5_conserves`, (A) from
`applyForestHalf_caps` per `i`, and (G) from `exec_authz_grounds_in_graph ∘ applyForestHalf_authz`
per `i`. -/
theorem forestAbsStep_forward {ι : Type v} [Fintype ι] [DecidableEq ι]
    (cells cells' : ι → KernelState) (ft : ForestTurn ι)
    (hbind : ∑ i, ft.δ i = 0)
    (h : forestApply cells ft = some cells') :
    forestAbsStep ft (forestAbsOf cells) (forestAbsOf cells') := by
  have hhalf := forestApply_atomic h
  refine ⟨?_, ?_, ?_⟩
  · -- (C5) cross-family conservation: the JOINT family total is preserved.
    show forestJointBalance (forestAbsOf cells') = forestJointBalance (forestAbsOf cells)
    rw [forestJointBalance_forestAbsOf, forestJointBalance_forestAbsOf]
    exact forestApply_cg5_conserves hbind h
  · -- (A) authority frame on every cell.
    intro i
    show (absOf (cells' i)).authGraph = (absOf (cells i)).authGraph
    simp only [absOf]
    rw [applyForestHalf_caps (hhalf i)]
  · -- (G) grounding on every cell.
    intro i
    show ft.actorA i = ft.srcA i ∨ (absOf (cells i)).authGraph.has (ft.actorA i) (ft.srcA i)
    simp only [absOf]
    exact exec_authz_grounds_in_graph (cells i).caps
      { actor := ft.actorA i, src := ft.srcA i, dst := ft.srcA i, amt := ft.δ i }
      (applyForestHalf_authz (hhalf i))

/-- Turn-index-closed form: every committed forest step under the Σ=0 binding is matched by a
`ForestAbsStep` (the forest turn existentially witnessed). -/
theorem forestAbsStep_forward_exists {ι : Type v} [Fintype ι] [DecidableEq ι]
    (cells cells' : ι → KernelState) (ft : ForestTurn ι)
    (hbind : ∑ i, ft.δ i = 0)
    (h : forestApply cells ft = some cells') :
    ForestAbsStep (forestAbsOf cells) (forestAbsOf cells') :=
  ⟨ft, forestAbsStep_forward cells cells' ft hbind h⟩

/-- Refines-shape: there is an abstract successor `p' = forestAbsOf cells'` such that
`forestAbsStep ft (forestAbsOf cells) p'`. -/
theorem forestAbsStep_refines {ι : Type v} [Fintype ι] [DecidableEq ι]
    (cells cells' : ι → KernelState) (ft : ForestTurn ι)
    (hbind : ∑ i, ft.δ i = 0)
    (h : forestApply cells ft = some cells') :
    ∃ p', p' = forestAbsOf cells' ∧ forestAbsStep ft (forestAbsOf cells) p' :=
  ⟨forestAbsOf cells', rfl, forestAbsStep_forward cells cells' ft hbind h⟩

/-! ## §7 — Lifting the N-ary square to whole forest runs. -/

/-- The reflexive-transitive closure of committed, Σ=0-bound `forestApply`-steps over the family.
Head-recursive. -/
inductive ForestRun {ι : Type v} [Fintype ι] [DecidableEq ι] :
    (ι → KernelState) → (ι → KernelState) → Prop where
  | refl (cells : ι → KernelState) : ForestRun cells cells
  | step {cells cells' Q : ι → KernelState} {ft : ForestTurn ι}
      (hbind : ∑ i, ft.δ i = 0)
      (s : forestApply cells ft = some cells') (rest : ForestRun cells' Q) : ForestRun cells Q

/-- The reflexive-transitive closure of `ForestAbsStep` — the run-level N-ary abstract LTS. -/
inductive ForestAbsRun {ι : Type v} [Fintype ι] :
    (ι → AbstractState) → (ι → AbstractState) → Prop where
  | refl (p : ι → AbstractState) : ForestAbsRun p p
  | step {p p' p'' : ι → AbstractState}
      (s : ForestAbsStep p p') (rest : ForestAbsRun p' p'') : ForestAbsRun p p''

/-- Every concrete `ForestRun` (each step Σ=0-bound) is matched by a `ForestAbsRun` between the
forest-abstractions of its endpoints. The square is stable under iteration. -/
theorem forestAbsRun_forward {ι : Type v} [Fintype ι] [DecidableEq ι]
    {P Q : ι → KernelState} (hrun : ForestRun P Q) :
    ForestAbsRun (forestAbsOf P) (forestAbsOf Q) := by
  induction hrun with
  | refl P => exact ForestAbsRun.refl _
  | @step cells cells' Q ft hbind s _ ih =>
      exact ForestAbsRun.step (forestAbsStep_forward_exists cells cells' ft hbind s) ih

/-! ## §8 — Non-vacuity: the binding and the grounding conjuncts do real work. -/

/-- The joint family total is preserved by any `forestAbsStep` — projecting out the (C5)
conjunct. -/
theorem forestAbsStep_conserves {ι : Type v} [Fintype ι] {ft : ForestTurn ι}
    {p p' : ι → AbstractState} (h : forestAbsStep ft p p') :
    forestJointBalance p' = forestJointBalance p := h.1

/-- Every half is authorized in its own authority graph — projecting out the (G) conjunct. -/
theorem forestAbsStep_grounded {ι : Type v} [Fintype ι] {ft : ForestTurn ι}
    {p p' : ι → AbstractState} (h : forestAbsStep ft p p') :
    ∀ i, ft.actorA i = ft.srcA i ∨ (p i).authGraph.has (ft.actorA i) (ft.srcA i) := h.2.2

/-- `forestAbsStep` is not the always-true relation: a turn over `ι = Unit` whose sole incidence
has actor ≠ src over the empty authority graph is not grounded, so no `forestAbsStep` holds for
it. The grounding conjunct (G) is not vacuous. -/
theorem forestAbsStep_not_vacuous :
    ∃ (ft : ForestTurn Unit) (p p' : Unit → AbstractState), ¬ forestAbsStep ft p p' := by
  refine ⟨{ actorA := fun _ => 0, srcA := fun _ => 1, δ := fun _ => 0, sid := 0 },
          (fun _ => { balanceTotal := 0, authGraph := fun _ _ => False }),
          (fun _ => { balanceTotal := 0, authGraph := fun _ _ => False }), ?_⟩
  rintro ⟨_, _, hg⟩
  rcases hg () with hown | hreach
  · exact absurd hown (by decide)
  · obtain ⟨_, hedge⟩ := hreach
    exact hedge

/-- A declared family of half-deltas need not sum to zero — the predicate to refute. -/
def FakeForestBalances {ι : Type v} [Fintype ι] (d : ι → ℤ) : Prop := ∑ i, d i = 0

/-- The CG-5 Σ=0 binding is a genuine restriction: there exist forest half-deltas that do not
sum to zero (over `ι = Bool`, deltas `1` and `2`, sum `= 3 ≠ 0`). Cross-family admissibility
is strictly stronger than the per-ledger conjunction; the binding must be hypothesized, never
derived. -/
theorem forestAbsStep_needs_binding :
    ∃ d : Bool → ℤ, ¬ FakeForestBalances d := by
  refine ⟨fun b => if b then 1 else 2, ?_⟩
  unfold FakeForestBalances
  rw [Fintype.sum_bool]
  decide

/-! ## §9 — The bilateral case is the `ι = Fin 2` slice.

`CrossCellLTS.crossAbsStep` is `forestAbsStep` at `ι = Fin 2`: the two-cell family total
`Σ_{Fin 2}` equals `jointBalance`, and the bilateral binding `halves_sum_zero` is the `Fin 2`
slice of `Σ δ = 0`. -/

/-- A `Fin 2`-forest from a bilateral `BiTurn`: incidence `0` is A's debit half (delta `halfA`),
incidence `1` is B's credit half (delta `halfB`). -/
def biToForest (bt : BiTurn) : ForestTurn (Fin 2) where
  actorA := fun i => i.cases bt.actorA (fun _ => bt.actorB)
  srcA   := fun i => i.cases bt.srcA (fun _ => bt.dstB)
  δ      := fun i => i.cases (halfA bt) (fun _ => halfB bt)
  sid    := bt.sid

/-- The `Fin 2`-forest's Σ=0 binding is the bilateral `halves_sum_zero`:
`Σ_{Fin 2} (biToForest bt).δ = halfA bt + halfB bt = 0`. -/
theorem biToForest_balanced (bt : BiTurn) : ∑ i, (biToForest bt).δ i = 0 := by
  rw [Fin.sum_univ_two]
  show halfA bt + halfB bt = 0
  exact halves_sum_zero bt

/-- At `ι = Fin 2`, `forestJointBalance p = CrossCellLTS.jointBalance (p 0, p 1)`. The N-ary
measure restricts to the bilateral one. -/
theorem forestJointBalance_two (p : Fin 2 → AbstractState) :
    forestJointBalance p = CrossCellLTS.jointBalance (p 0, p 1) := by
  unfold forestJointBalance CrossCellLTS.jointBalance
  rw [Fin.sum_univ_two]

/-- A `Fin 2` forest step `forestAbsStep (biToForest bt) p p'` entails the bilateral
`CrossCellLTS.crossAbsStep bt (p 0, p 1) (p' 0, p' 1)`: the bilateral square is exactly the
two-cell slice of the N-ary one. -/
theorem forestAbsStep_two_refines_crossAbs (bt : BiTurn) (p p' : Fin 2 → AbstractState)
    (h : forestAbsStep (biToForest bt) p p') :
    CrossCellLTS.crossAbsStep bt (p 0, p 1) (p' 0, p' 1) := by
  obtain ⟨hc5, hA, hG⟩ := h
  refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · -- (C5) the bilateral joint total is the N-ary family total.
    show CrossCellLTS.jointBalance (p' 0, p' 1) = CrossCellLTS.jointBalance (p 0, p 1)
    rw [← forestJointBalance_two, ← forestJointBalance_two]; exact hc5
  · -- (A) A-side authority frame: incidence 0.
    exact hA 0
  · -- (A) B-side authority frame: incidence 1.
    exact hA 1
  · -- (G) A-side grounding: incidence 0 reads `actorA`/`srcA`.
    exact hG 0
  · -- (G) B-side grounding: incidence 1 reads `actorB`/`dstB`.
    exact hG 1

/-! ## §10 — Axiom-hygiene tripwires. -/

#assert_axioms applyForestHalf_caps
#assert_axioms applyForestHalf_accounts
#assert_axioms applyForestHalf_authz
#assert_axioms applyForestHalf_total
#assert_axioms forestApply_atomic
#assert_axioms forestJointBalance_forestAbsOf
#assert_axioms forestApply_cg5_conserves
#assert_axioms forestAbsStep_forward
#assert_axioms forestAbsStep_forward_exists
#assert_axioms forestAbsStep_refines
#assert_axioms forestAbsRun_forward
#assert_axioms forestAbsStep_conserves
#assert_axioms forestAbsStep_grounded
#assert_axioms forestAbsStep_not_vacuous
#assert_axioms forestAbsStep_needs_binding
#assert_axioms biToForest_balanced
#assert_axioms forestJointBalance_two
#assert_axioms forestAbsStep_two_refines_crossAbs

/-! ## §11 — Summary.

The N-ary cross-cell forward-simulation square is closed. `forestApply` is the executable forest
transition (fail-closed, atomic). `forestApply_cg5_conserves` proves joint Σ-conservation given
`Σ δ = 0` (explicit HYPOTHESIS, never derived). `forestAbsStep_forward` matches every committed
forest step with the N-ary abstract LTS edge; `forestAbsRun_forward` lifts to whole histories.
Non-vacuous (`forestAbsStep_not_vacuous`, `forestAbsStep_needs_binding`), axiom-clean.
The bilateral square is the `ι = Fin 2` slice (`forestAbsStep_two_refines_crossAbs`).

-- OPEN: the CONTENDED / adversary-scheduler case — concurrent overlapping forests (a cell
--   incident to two forests at once), the coinductive `Boundary` over interleaved forests —
--   remains out of scope.
-/

end Dregg2.Proof.ForestLTS
