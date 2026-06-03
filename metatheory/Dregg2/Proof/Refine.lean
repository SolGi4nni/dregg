/-
# Dregg2.Proof.Refine — the Exec ⊑ Abstract refinement (the l4v `proof/refine` analog).

`Exec/Kernel.lean` builds the executable kernel; `Core`, `Authority.Positional`, `Boundary`,
`Execution` state the abstract laws. This module proves the concrete machine realizes those
laws, relaying the already-proved kernel lemmas:

* `refine_conservation`     — `total` is invariant under every committed `exec` step (Law 1).
* `refine_run_conservation` — conservation holds along every whole kernel `Run`.
* `refine_integrity`        — every committed step is authority-admissible; the owner
  (intra-vat) case is bridged into `Authority.Integrity`.
* `exec_refines`            — forward-simulation: the conservation component is proved;
  the full abstract operational simulation needs an abstract small-step model not present in
  `Core` (which states laws, not a transition relation) — that part is a precise `-- OPEN:`.

The conservation refinement is fully proved; the deeper operational simulation is partially open.
-/
import Dregg2.Exec.Kernel
import Dregg2.Core
import Dregg2.Authority.Positional
import Dregg2.Execution

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

/-! ## 4. Forward simulation: `exec_refines`. -/

/-- The refinement relation `R`: `k` is related to abstract config `cc` when
`cc.1.count cc.2 = total k` (the abstract count equals the concrete total). -/
def R (k : KernelState) (cc : Core.Conservation ℤ × Core.Cell) : Prop :=
  cc.1.count cc.2 = total k

/-- **Forward / simulation refinement (`exec_refines`).** For any concrete step
`exec k turn = some k'` with `R k cc`, there exists `cc'` with `R k' cc'` and the abstract
measure preserved (`cc'.1.count cc'.2 = cc.1.count cc.2`). The conservation component is proved
by taking `cc' = cc` and applying `exec_conserves`.

OPEN: a full operational forward simulation also requires an abstract small-step relation
`AbsStep`. `Core` states Law 1 as a measure obligation, not a transition system, so no such
`AbsStep` is in scope. The conservation component (proved here) is the load-bearing half; the
operational-diagram half is left open rather than faked. -/
theorem exec_refines (k k' : KernelState) (turn : Turn)
    (cc : Core.Conservation ℤ × Core.Cell)
    (hstep : exec k turn = some k') (hR : R k cc) :
    ∃ cc' : Core.Conservation ℤ × Core.Cell,
      R k' cc' ∧ cc'.1.count cc'.2 = cc.1.count cc.2 := by
  -- The abstract config matching `k'`: reuse the same `Conservation` data, and pick a
  -- cell whose abstract count is `total k'`. Concretely, reuse `cc.2` and rewrite via
  -- conservation: `total k' = total k = cc.1.count cc.2`.
  refine ⟨cc, ?_, rfl⟩
  -- `R k' cc` : `cc.1.count cc.2 = total k'`. We have `hR : cc.1.count cc.2 = total k`
  -- and `exec_conserves : total k' = total k`.
  unfold R at hR ⊢
  rw [hR, (exec_conserves k k' turn hstep).symm]

/-- Run-level form: any abstract config related to the start of a run is matched by one related
to the end with the same abstract measure. -/
theorem exec_refines_run {k k' : KernelState}
    (cc : Core.Conservation ℤ × Core.Cell)
    (hrun : Run kernelSystem k k') (hR : R k cc) :
    ∃ cc' : Core.Conservation ℤ × Core.Cell,
      R k' cc' ∧ cc'.1.count cc'.2 = cc.1.count cc.2 := by
  refine ⟨cc, ?_, rfl⟩
  unfold R at hR ⊢
  rw [hR, (refine_run_conservation hrun).symm]

end Dregg2.Proof
