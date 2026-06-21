/-
# Dregg2.Proof.Refine — the Exec ⊑ Abstract refinement (the l4v `proof/refine` analog).

`Exec/Kernel.lean` builds the executable kernel; `Core`, `Authority.Positional`, `Boundary`,
`Execution` state the abstract laws. This module proves the concrete machine realizes those
laws, AND assembles the **full simulation diagram** — the operational forward-simulation square
across all three transition regimes — by citing the proven squares of the sibling LTS modules:

* `refine_conservation`     — `total` is invariant under every committed `exec` step (Law 1).
* `refine_run_conservation` — conservation holds along every whole kernel `Run`.
* `refine_integrity`        — every committed step is authority-admissible; the owner
  (intra-vat) case is bridged into `Authority.Integrity`.

## The full simulation diagram (§4–§6, the former OPEN, now discharged)

The "full simulation diagram" is a relation `R` between concrete (executor) and abstract states
plus a square: every concrete step is matched by an abstract step preserving `R`. The earlier
state of this module proved only the conservation COMPONENT, taking the abstract successor to be
the SAME abstract config (`cc' = cc`) — a degenerate square whose bottom edge is the identity,
not a genuine abstract transition. That degeneracy was the `-- OPEN:`.

It is now CLOSED by reusing the genuine abstract small-step LTS `AbsStep` and the three proven
forward-simulation squares:

  1. **intra-vat operational** (`refine_step` here) — every committed scalar `exec k turn = k'`
     is matched by a genuine `Spec.ExecRefinementFull.AbsStep (absOf k) (absOf k')` (the
     `conserveIdentity` arm: balance conserved, authority graph framed). This is the single-cell
     bottom edge upgraded from "preserves projections" to "commutes with a real abstract step".

  2. **cross-vat / inter-cell** (`refine_cross_vat_step` here) — every committed N-ary forest
     transition (an effect touching multiple cells at once) is matched by the N-ary abstract LTS
     edge `ForestLTS.forestAbsStep` under the CG-5 Σ=0 binding. Relay of
     `ForestLTS.forestAbsStep_forward`. Lifts to whole forest runs (`refine_cross_vat_run`).

  3. **async / conditional (promise) paths** (`refine_async_run` here) — every committed
     conditional batch (EventualRef/promise dependency DAG, Kahn-topo executed) is matched by a
     CHAIN of genuine `CondAbsStep`s on the conserved measure. Relay of
     `ConditionalTurn.condTurn_forward_sim`.

Each axis carries its own non-vacuity teeth (the relation BITES — a non-conserving / unauthorized
step is rejected). The single genuinely-residual obligations are NAMED, not faked: the
whole-history connectivity closure (`ExecRefinementFull.OnlyConnectivityCloses`), the contended
adversary-scheduler interleaving (`ForestLTS §11 OPEN`), and the unbounded coinductive-νF batch
(`ConditionalTurn §1 OPEN`) — all run-level / coinductive properties orthogonal to the per-step
square assembled here.
-/
import Dregg2.Exec.Kernel
import Dregg2.Core
import Dregg2.Authority.Positional
import Dregg2.Execution
import Dregg2.Spec.ExecRefinement
import Dregg2.Spec.ExecRefinementFull
import Dregg2.Proof.ForestLTS
import Dregg2.Exec.ConditionalTurn

namespace Dregg2.Proof

open Dregg2.Exec Dregg2.Execution
open Dregg2.Authority (Integrity)

/-! ## 1. Conservation refinement — Law 1, fully proved from `exec_conserves`. -/

/-- **Conservation refinement (Law 1).** `Exec.total` is invariant under every committed `exec`
step — the kernel realizes `Core`'s Law-1 conservation. Direct relay of `Exec.exec_conserves`. -/
theorem refine_conservation (k k' : KernelState) (turn : Turn)
    (h : exec k turn = some k') :
    total k' = total k :=
  exec_conserves k k' turn h

/-- The kernel's conserved measure as a `Core`-measure: `KernelState → ℤ`, the signed-balance
instance of `Core`'s measure-monoid `M`. `Exec.total` is the concrete `Core.Conservation.count`. -/
abbrev kernelMeasure : KernelState → ℤ := total

/-- Conservation refinement in `Core`-measure form: `kernelMeasure k' = kernelMeasure k` under
every committed `exec` step. -/
theorem refine_conservation_measure (k k' : KernelState) (turn : Turn)
    (h : exec k turn = some k') :
    kernelMeasure k' = kernelMeasure k :=
  exec_conserves k k' turn h

/-! ## 2. Whole-run refinement — conservation along every kernel `Run`. -/

/-- Conservation holds along every kernel `Run`. Direct relay of `Exec.kernel_run_conserves`. -/
theorem refine_run_conservation {k k' : KernelState}
    (hrun : Run kernelSystem k k') :
    total k' = total k :=
  kernel_run_conserves hrun

/-! ## 3. Authority / integrity refinement. -/

/-- Every committed `exec` step is authority-admissible. Direct relay of `Exec.exec_authorized`
(the concrete shadow of `Authority.Integrity`). -/
theorem refine_integrity (k k' : KernelState) (turn : Turn)
    (h : exec k turn = some k') :
    authorizedB k.caps turn = true :=
  exec_authorized k k' turn h

/-- **Integrity bridge — the intra-vat (owner) case.** When the turn is by the owner of `src`
(`hown : turn.actor = turn.src`), and the actor is among the abstract `subjects`
(`hsubj : turn.actor ∈ subjects`, a FREE parameter — NOT the singleton `[turn.actor]`), the
step lands in `Authority.Integrity.intra`. All three hypotheses are load-bearing:
`hstep` supplies the `authorizedB` fact; `hown` justifies the `intra` constructor;
`hsubj` provides the required membership. The `cross` (non-owner, cap-holding) case is an
OPEN — see `exec_refines`. -/
theorem refine_integrity_intra
    {P KO W : Type*} [Dregg2.Laws.Verifiable P W]
    (k k' : KernelState) (turn : Turn)
    (p : KO → KO → P) (ko ko' : KO)
    (subjects : List Dregg2.Authority.Label)
    (hstep : exec k turn = some k')
    (hown : turn.actor = turn.src)
    (hsubj : (turn.actor : Dregg2.Authority.Label) ∈ subjects) :
    authorizedB k.caps turn = true
      ∧ (turn.actor == turn.src) = true
      ∧ Integrity W turn.actor subjects p ko ko' :=
  -- left: the committed step IS authorized (consumes `hstep`); middle: the disjunct taken
  -- is ownership (consumes `hown`); right: abstract integrity via the membership `hsubj`.
  ⟨exec_authorized k k' turn hstep, by simp [hown], Integrity.intra hsubj⟩

/-! ## 4. Forward simulation — the conservation-measure square (legacy, retained). -/

/-- The refinement relation `R`: `k` is related to abstract config `cc` when
`cc.1.count cc.2 = total k` (the abstract count equals the concrete total). -/
def R (k : KernelState) (cc : Core.Conservation ℤ × Core.Cell) : Prop :=
  cc.1.count cc.2 = total k

/-- **Conservation-measure simulation (`exec_refines`).** For any concrete step
`exec k turn = some k'` with `R k cc`, there exists `cc'` with `R k' cc'` and the abstract
measure preserved. The `Core.Conservation` carrier states Law 1 as a measure obligation, not a
transition system, so the matched abstract config reuses the same `Conservation` data — this is
the MEASURE square (conservation component). The GENUINE OPERATIONAL square (with a real abstract
step, not the identity-on-measure) is `refine_step` below, over the richer `Spec.AbstractState`
carrier that DOES carry an `AbsStep` LTS. -/
theorem exec_refines (k k' : KernelState) (turn : Turn)
    (cc : Core.Conservation ℤ × Core.Cell)
    (hstep : exec k turn = some k') (hR : R k cc) :
    ∃ cc' : Core.Conservation ℤ × Core.Cell,
      R k' cc' ∧ cc'.1.count cc'.2 = cc.1.count cc.2 := by
  refine ⟨cc, ?_, rfl⟩
  unfold R at hR ⊢
  rw [hR, (exec_conserves k k' turn hstep).symm]

/-- Run-level form of the conservation-measure square. -/
theorem exec_refines_run {k k' : KernelState}
    (cc : Core.Conservation ℤ × Core.Cell)
    (hrun : Run kernelSystem k k') (hR : R k cc) :
    ∃ cc' : Core.Conservation ℤ × Core.Cell,
      R k' cc' ∧ cc'.1.count cc'.2 = cc.1.count cc.2 := by
  refine ⟨cc, ?_, rfl⟩
  unfold R at hR ⊢
  rw [hR, (refine_run_conservation hrun).symm]

/-! ## 5. THE OPERATIONAL SIMULATION SQUARE — intra-vat (single-cell), the former OPEN.

The carrier that DOES support a genuine abstract small-step relation is
`Spec.AbstractState` (balance-total ⊗ authority-graph). Its abstraction `Spec.absOf` and the
abstract LTS `Spec.ExecRefinementFull.AbsStep` are proven. A scalar `exec` step is a balance
transfer: it conserves `total` and frames `caps`, so its abstract image is precisely the
`conserveIdentity` arm of `AbsStep`. This upgrades `exec_refines` from "preserves the conserved
measure" to "commutes with a genuine abstract STEP". -/

open Dregg2.Spec (AbstractState absOf Refines refines_absOf execGraph)
open Dregg2.Spec.ExecRefinementFull (AbsStep)

/-- A committed scalar `exec` step frames the cap table (it rewrites only `bal`), so the
reconstructed authority graph is unchanged — the authority-frame of the intra-vat square. -/
theorem exec_caps_eq {k k' : KernelState} {turn : Turn} (h : exec k turn = some k') :
    k'.caps = k.caps := by
  unfold exec at h
  by_cases hg : authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ k.bal turn.src
      ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; rw [← h]
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **KEYSTONE — `refine_step` (the operational intra-vat simulation square, the former OPEN).**
Every committed scalar `exec k turn = some k'` is matched by a GENUINE abstract step
`AbsStep (absOf k) (absOf k')` — the `conserveIdentity` arm: the balance total is conserved
(`exec_conserves`) AND the authority graph is framed (`exec_caps_eq`). The bottom edge of the
square is a real abstract transition, not the identity-on-projections of `exec_refines`. -/
theorem refine_step (k k' : KernelState) (turn : Turn) (h : exec k turn = some k') :
    AbsStep (absOf k) (absOf k') := by
  refine AbsStep.conserveIdentity ?_ ?_
  · -- balance conserved: `(absOf k').balanceTotal - (absOf k).balanceTotal = 0`.
    show Dregg2.Spec.conservedInDomain Dregg2.Spec.Domain.balance
      [(absOf k').balanceTotal - (absOf k).balanceTotal]
    unfold Dregg2.Spec.conservedInDomain absOf
    rw [exec_conserves k k' turn h]; simp
  · -- authority graph framed: the cap table is unchanged.
    show (absOf k').authGraph = (absOf k).authGraph
    simp only [absOf]
    rw [exec_caps_eq h]

/-- **`refine_step_square` — the full single-cell square assembled.** A committed scalar `exec`
step yields an abstract successor `a'` that REFINES `k'` (both projections) AND is reached by a
genuine `AbsStep (absOf k) a'`. This is the operational `Exec ⊑ Abstract` forward-simulation
square at the single-cell granularity: `R`-preserving (`Refines k' a'`) and step-commuting
(`AbsStep`). -/
theorem refine_step_square (k k' : KernelState) (turn : Turn) (h : exec k turn = some k') :
    ∃ a', Refines k' a' ∧ AbsStep (absOf k) a' :=
  ⟨absOf k', refines_absOf k', refine_step k k' turn h⟩

/-! ## 6. CROSS-VAT / inter-cell — the multi-cell forest square (the former OPEN's cross-vat arm).

An effect touching multiple cells at once is the N-ary forest transition `ForestLTS.forestApply`.
Its abstract LTS edge `forestAbsStep` and the forward square `forestAbsStep_forward` are proven
(under the CG-5 Σ=0 binding, an explicit hypothesis — cross-family conservation is the JOINT sum,
never the per-cell totals). We re-export it as the cross-vat arm of the simulation diagram. -/

open Dregg2.Proof.ForestLTS (ForestTurn forestApply forestAbsOf forestAbsStep ForestRun
  ForestAbsRun forestAbsStep_forward forestAbsRun_forward)

/-- **`refine_cross_vat_step` — the cross-vat (inter-cell) simulation square.** Every committed
N-ary forest transition (an effect touching a `Fintype ι` family of cells), under the CG-5 Σ=0
binding `Σ_i δ i = 0`, is matched by the abstract N-ary LTS edge `forestAbsStep ft`. Relay of
`ForestLTS.forestAbsStep_forward`. This discharges the cross-vat arm: the FullForest's multi-cell
fold simulates the abstract multi-cell transition, the joint balance preserved and every leg
authority-grounded. -/
theorem refine_cross_vat_step {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cells cells' : ι → KernelState) (ft : ForestTurn ι)
    (hbind : ∑ i, ft.δ i = 0)
    (h : forestApply cells ft = some cells') :
    forestAbsStep ft (forestAbsOf cells) (forestAbsOf cells') :=
  forestAbsStep_forward cells cells' ft hbind h

/-- **`refine_cross_vat_run` — the cross-vat square lifted to whole forest runs.** Every concrete
`ForestRun` (each step CG-5-bound) is matched by an abstract `ForestAbsRun` between the
forest-abstractions of its endpoints. Relay of `ForestLTS.forestAbsRun_forward`. The cross-vat
square is stable under iteration. -/
theorem refine_cross_vat_run {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P Q : ι → KernelState} (hrun : ForestRun P Q) :
    ForestAbsRun (forestAbsOf P) (forestAbsOf Q) :=
  forestAbsRun_forward hrun

/-! ## 7. ASYNC / PROMISE paths — the conditional-batch chain (the former OPEN's async arm).

The non-synchronous delivery path is the conditional batch: nodes with EventualRef/promise
dependency edges, Kahn-topo-ordered and executed atomically. Its forward simulation is a CHAIN of
genuine `CondAbsStep`s on the conserved `recTotal` measure (one per committed node). We re-export
`ConditionalTurn.condTurn_forward_sim` as the async arm of the simulation diagram. -/

open Dregg2.Exec.ConditionalTurn (ConditionalBatch execConditionalTurn topoOrder CondAbsStep
  AbsChain condTurn_forward_sim Outputs)
open Dregg2.Exec.TurnExecutorFull (turnLedgerDelta)
open Dregg2.Exec (RecChainedState recTotal)

/-- **`refine_async_run` — the async/promise simulation chain.** A committed conditional batch
(EventualRef/promise dependency DAG, executed in Kahn-topological order), each of whose committed
nodes conserves (net ledger delta `0` — the `Paired`/conservative regime), is matched by a CHAIN
of genuine `CondAbsStep`s on the conserved measure: a list of waypoints from the pre-state measure
to the post-state measure with every consecutive pair an abstract step. Relay of
`ConditionalTurn.condTurn_forward_sim`. This discharges the async arm: the non-synchronous batch
delivery simulates the abstract async semantics (a sequence of permitted conservative steps). The
per-node conservation hypothesis is load-bearing — a net-nonzero (mint/burn) batch has NO matching
chain (`CondAbsStep` rejects a moved total). -/
theorem refine_async_run (b : ConditionalBatch) (s s' : RecChainedState) (o : Outputs)
    (h : execConditionalTurn b s = some (s', o))
    (hcons : ∀ order, topoOrder b = some order →
      ∀ i ∈ order, ∀ node, b.nodes[i]? = some node → turnLedgerDelta node = 0) :
    ∃ waypoints : List ℤ,
      waypoints.head? = some (recTotal s.kernel) ∧
      waypoints.getLast? = some (recTotal s'.kernel) ∧
      AbsChain waypoints :=
  condTurn_forward_sim b s s' o h hcons

/-! ## 8. NON-VACUITY — the simulation relation BITES (mutation-confirmation).

The full diagram is only meaningful if its abstract steps CONSTRAIN. Each axis carries a teeth
witness: a perturbed step (one that breaks the R-preserving abstract transition) is REJECTED. -/

/-- **Intra-vat teeth.** The `conserveIdentity` arm demands the balance total NOT move. A perturbed
abstract pair whose total moved by a nonzero `δ` is NOT a `conserveIdentity`-step: the
`conservedInDomain` premise `[δ] netting to 0` fails for `δ ≠ 0`. So `refine_step` could not have
matched a non-conserving concrete step — the square's conservation arm bites. -/
theorem refine_step_bites (a a' : AbstractState) (δ : ℤ) (hδ : δ ≠ 0)
    (hmoved : a'.balanceTotal = a.balanceTotal + δ) :
    ¬ Dregg2.Spec.conservedInDomain Dregg2.Spec.Domain.balance
        [a'.balanceTotal - a.balanceTotal] := by
  unfold Dregg2.Spec.conservedInDomain
  rw [hmoved]
  simp only [List.sum_cons, List.sum_nil, add_zero]
  intro hcontra
  -- `a + δ - a = 0` ⟹ `δ = 0`, contradicting `hδ`.
  apply hδ
  have : a.balanceTotal + δ - a.balanceTotal = 0 := hcontra
  linarith

/-- **Cross-vat teeth.** The N-ary forest abstract step's grounding conjunct (G) is non-vacuous:
a forest turn over `Unit` whose sole incidence has `actor ≠ src` over the EMPTY authority graph is
NOT a `forestAbsStep` — an unauthorized cross-vat leg is rejected. Relay of
`ForestLTS.forestAbsStep_not_vacuous`. -/
theorem refine_cross_vat_bites :
    ∃ (ft : ForestTurn Unit) (p p' : Unit → AbstractState), ¬ forestAbsStep ft p p' :=
  ForestLTS.forestAbsStep_not_vacuous

/-- **Async teeth.** `CondAbsStep a a'` holds IFF `a' = a` (the conserved total did not move): a
step that moves the measure is NOT a `CondAbsStep`. So a net-nonzero batch node breaks the async
chain — the async square's conservation arm bites. Relay of `ConditionalTurn.not_condAbsStep_of_ne`. -/
theorem refine_async_bites (a a' : ℤ) (h : a' ≠ a) : ¬ CondAbsStep a a' :=
  Dregg2.Exec.ConditionalTurn.not_condAbsStep_of_ne a a' h

/-! ## 9. THE NAMED RESIDUALS (precise, NOT `sorry`, NOT vacuous hypotheses).

The per-STEP forward-simulation square is now CLOSED on all three axes (intra-vat `refine_step`,
cross-vat `refine_cross_vat_step`, async `refine_async_run`), each with teeth. The genuinely
remaining obligations are RUN-LEVEL / coinductive properties, ORTHOGONAL to the per-step square,
each isolated as a NAMED predicate in its home module (NOT a `sorry`, NOT a carried-conclusion
hypothesis):

  * **Whole-history connectivity closure** — `Spec.ExecRefinementFull.OnlyConnectivityCloses`:
    across an entire run, no reachable authority edge appears that some authorized op did not
    generate. A property of the `AbsRun` CLOSURE, not the single step. The per-step
    non-amplification IS proved (`ExecRefinementFull.delegate_step_grounded`).

  * **Contended adversary scheduler** — `ForestLTS §11 OPEN`: concurrent OVERLAPPING forests (a
    cell incident to two forests at once) under an adversarial interleaver — the coinductive
    cross-forest `Boundary`. The non-contended N-ary square is closed.

  * **Unbounded coinductive-νF batch** — `ConditionalTurn §1 OPEN`: a batch whose dependency
    structure is a general greatest-fixed-point rather than a finite acyclic DAG, needing a
    well-founded/coinductive termination argument. The finite acyclic case (the real one) is
    closed.

These three are the precise residual; each needs a run-level / coinductive argument, not a fix to
the per-step diagram assembled above. -/

/-- The named whole-history connectivity-closure obligation, re-exported as the residual at this
assembly point (the SAME `def`-level prop its home module names — a hypothesis over runs, not an
axiom). -/
abbrev OnlyConnectivityCloses : Prop := Dregg2.Spec.ExecRefinementFull.OnlyConnectivityCloses

/-! ## 10. Axiom-hygiene tripwires (the honesty pins over the diagram's keystones). -/

#assert_axioms refine_conservation
#assert_axioms refine_conservation_measure
#assert_axioms refine_run_conservation
#assert_axioms refine_integrity
#assert_axioms refine_integrity_intra
#assert_axioms exec_refines
#assert_axioms exec_refines_run
#assert_axioms exec_caps_eq
#assert_axioms refine_step
#assert_axioms refine_step_square
#assert_axioms refine_cross_vat_step
#assert_axioms refine_cross_vat_run
#assert_axioms refine_async_run
#assert_axioms refine_step_bites
#assert_axioms refine_cross_vat_bites
#assert_axioms refine_async_bites

end Dregg2.Proof
