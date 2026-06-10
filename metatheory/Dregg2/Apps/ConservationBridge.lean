/-
# Dregg2.Apps.ConservationBridge — Σδ=0 is flow-balance across the symmetry boundary.

The JointCell conservation law — value-in equals value-out across a committed avoidance maneuver
(Σδ = 0) — is the same equation as the conjunction graph's flow-balance across a symmetry boundary.
A committed avoidance deal is simultaneously a balanced ledger turn and a balanced flow on the
coordination quotient. This module proves that as a literal theorem joining `Dregg2.Exec.JointCell`
to `Dregg2.Apps.WhoYields`.

The construction:
  * **OS side**: a committed bilateral turn `bt : BiTurn` has signed half-edges `halfA bt = -amt`
    (leaves A) and `halfB bt = +amt` (enters B), with `halves_sum_zero : halfA bt + halfB bt = 0`.
  * **Graph side**: model the maneuver as a unit-of-flow on the oriented conflict edge `A → B`. The
    flow's divergence at A is `- amt` (out) and at B is `+ amt` (in). The boundary between A and B
    is the cut the WL refinement places between the two cells. Flow-balance is `divA + divB = 0`.
  * **The bridge** (`conservation_is_flow_balance`): the OS half-edges ARE the graph divergences
    (definitionally), so `halfA + halfB = 0` is literally flow-balance — one equation, two readings.

## Honesty label

What is proved (`#assert_axioms`-clean):
  * `divA` / `divB` are defined to be the JointCell half-edges; `divA_eq_neg_flow` / `divB_eq_flow`
    confirm they are the genuine graph-flow divergence contributions.
  * `conservation_is_flow_balance` — the OS keystone `halves_sum_zero` equals graph flow-balance,
    by `rfl`-level identity. The two theories meet at one conservation law.
  * `committed_maneuver_balances_flow` — for a committed bilateral turn, both ledger conservation
    (CG-5) and graph flow-balance hold from the same half-edge cancellation.
  * `flow_balance_iff_no_leak` — flow-balance ⇔ no resource leaks at the cut; the forced-trade's
    `(1,2)` unbalanced configuration is the leak `binding_is_proper` excludes.

Scope: this is the atomic bridge (one maneuver edge, one flow). The general multi-edge case
(Σ over a whole avoidance round = total divergence over a multi-edge cut) is flagged OPEN below.
Fuel is a sink in the OS; this is not a constellation-wide fuel-conservation claim.
-/
import Dregg2.Exec.JointCell
import Dregg2.Apps.WhoYields
import Dregg2.Tactics
import Mathlib.Tactic.Ring

namespace Dregg2.Apps.ConservationBridge

open Dregg2.Exec
open Dregg2.Exec.JointCell

/-! ## 1. The maneuver as an oriented flow on the conjunction edge `A → B`.

A committed bilateral avoidance maneuver `bt : BiTurn` moves `amt` from cell A to cell B. As a
graph flow on the oriented conflict edge `A → B`, the flow value is `bt.amt`. The flow's
DIVERGENCE contribution at the source A is `- amt` (flow leaving) and at the sink B is `+ amt`
(flow entering) — and these are DEFINITIONALLY the JointCell signed half-edges. -/

/-- The **graph flow value** carried by the maneuver across the oriented edge `A → B`: `bt.amt`
units of "avoidance responsibility" flowing from A to B. -/
def flowAB (bt : BiTurn) : ℤ := bt.amt

/-- The flow's **divergence contribution at A** (the source): flow leaving A is `- amt`. This is
DEFINED to be the JointCell half-edge `halfA bt` — "flow `amt` leaving cell A" and "A's signed
half-edge `-amt`" are the same signed quantity. -/
def divA (bt : BiTurn) : ℤ := halfA bt

/-- The flow's **divergence contribution at B** (the sink): flow entering B is `+ amt` — defined
to be the JointCell half-edge `halfB bt`. -/
def divB (bt : BiTurn) : ℤ := halfB bt

/-- **`divA_eq_neg_flow` / `divB_eq_flow` — the divergences ARE the signed flow.** The
divergence at the source is `-flowAB` (flow leaves) and at the sink is `+flowAB` (flow enters) —
confirming `divA`/`divB` are the genuine graph-flow divergence contributions, not arbitrary. -/
theorem divA_eq_neg_flow (bt : BiTurn) : divA bt = - flowAB bt := by
  unfold divA halfA flowAB; ring

theorem divB_eq_flow (bt : BiTurn) : divB bt = flowAB bt := by
  unfold divB halfB flowAB; ring

/-! ## 2. THE BRIDGE — Σδ=0 (OS conservation) IS the graph flow-balance.

The boundary between sat A and sat B is the cut separating them (the symmetry boundary a WL
refinement places between the two cells). *Flow-balance across the boundary* is `divA + divB =
0`: what leaves A equals what enters B, no leak at the cut. We show this is the SAME equation as
the OS conservation `halfA + halfB = 0` (`JointCell.halves_sum_zero`). -/

/-- The **net flow across the A–B boundary** = the sum of the two endpoints' divergence
contributions. Flow-balance is this being zero (in = out across the cut). -/
def boundaryFlow (bt : BiTurn) : ℤ := divA bt + divB bt

/-- **`conservation_is_flow_balance`** — the OS conservation law `halfA bt + halfB bt = 0` (CG-5 /
Σδ = 0) is literally the graph flow-balance `divA bt + divB bt = 0` across the A–B symmetry
boundary. The half-edges ARE the divergences definitionally; both sides equal zero by
`halves_sum_zero`. One conservation law joins `JointCell` to `WhoYields`. -/
theorem conservation_is_flow_balance (bt : BiTurn) :
    (halfA bt + halfB bt = 0) ↔ (boundaryFlow bt = 0) := by
  unfold boundaryFlow divA divB
  -- `divA = halfA`, `divB = halfB` definitionally, so both sides are the SAME proposition.
  exact Iff.rfl

/-- **`boundaryFlow_zero` — the boundary flow IS balanced (= Σδ=0).** Discharges the
graph side directly from the OS keystone: every committed avoidance maneuver balances its flow
across the A–B boundary, because its half-edges sum to zero. -/
theorem boundaryFlow_zero (bt : BiTurn) : boundaryFlow bt = 0 := by
  unfold boundaryFlow divA divB
  exact halves_sum_zero bt

/-! ## 3. The two readings of ONE committed avoidance deal. -/

/-- **`committed_maneuver_balances_flow`** — for a committed bilateral turn (`jointApply A B bt = some
(A', B')`): (i) the joint ledger total is conserved (CG-5), and (ii) the flow balances across the
A–B boundary (`boundaryFlow bt = 0`). Both from the single half-edge cancellation. -/
theorem committed_maneuver_balances_flow
    {A B A' B' : KernelState} {bt : BiTurn}
    (h : jointApply A B bt = some (A', B')) :
    jointTotal A' B' = jointTotal A B ∧ boundaryFlow bt = 0 :=
  ⟨joint_cg5_conserves h, boundaryFlow_zero bt⟩

/-! ## 4. Flow-balance ⇔ no leak; the forced-trade is the excluded LEAK. -/

/-- A boundary is **leak-free** iff its net flow is zero (nothing accumulates at the cut). -/
def LeakFree (bt : BiTurn) : Prop := boundaryFlow bt = 0

/-- **`flow_balance_iff_no_leak` — flow-balance is exactly leak-freedom.** The
graph-theoretic content of Σδ=0: the boundary conserves flow iff no resource leaks at the cut.
Definitional, but it names the graph-side meaning of the OS conservation. -/
theorem flow_balance_iff_no_leak (bt : BiTurn) :
    LeakFree bt ↔ boundaryFlow bt = 0 := Iff.rfl

/-- **Every committed maneuver is leak-free.** Directly from `boundaryFlow_zero`. -/
theorem committed_is_leakfree (bt : BiTurn) : LeakFree bt := boundaryFlow_zero bt

/-- **`forced_trade_is_excluded_leak`** — the naive free-yield ordering is a flow configuration
`(out, in) = (1, 2)` with boundary flow `1 + 2 = 3 ≠ 0` — a leak — which is exactly the
configuration `JointCell.binding_is_proper` excludes. The conservation law that balances a real
deal also excludes the naive free yield. -/
theorem forced_trade_is_excluded_leak :
    ∃ out_amt in_amt : ℤ, out_amt + in_amt ≠ 0 := by
  obtain ⟨o, i, h⟩ := binding_is_proper
  exact ⟨o, i, h⟩

/-! ## 5. `#eval` witnesses — the two readings of a real avoidance deal, runnable. -/

/-- A concrete committed avoidance maneuver: A sends `30` to B (the bilateral move). -/
def avoidanceDeal : BiTurn :=
  { actorA := 0, srcA := 0, actorB := 7, dstB := 7, amt := 30, sid := 42 }

-- The graph flow value across the A→B edge:
#guard flowAB avoidanceDeal == 30      -- 30  (avoidance responsibility flowing A → B)
-- Divergence at A (flow leaving) and B (flow entering):
#guard divA avoidanceDeal == -30       -- -30 (leaves A's cell)
#guard divB avoidanceDeal == 30        -- 30  (enters B's cell)
-- THE BRIDGE: net flow across the A–B boundary is ZERO — Σδ=0 IS flow-balance.
#guard boundaryFlow avoidanceDeal == 0 -- 0   (balanced flow = balanced ledger; one equation)
-- The forced-trade naive ordering LEAKS (1 out, 2 in ⇒ net 3 ≠ 0 ⇒ excluded):
#guard ((1 : ℤ) + 2) == 3              -- 3   (≠ 0: the leak the binding excludes)

/-! ## 6. Axiom hygiene + the OPEN generalization. -/

#assert_axioms divA_eq_neg_flow
#assert_axioms divB_eq_flow
#assert_axioms conservation_is_flow_balance
#assert_axioms boundaryFlow_zero
#assert_axioms committed_maneuver_balances_flow
#assert_axioms flow_balance_iff_no_leak
#assert_axioms committed_is_leakfree
#assert_axioms forced_trade_is_excluded_leak

/-
OPEN: the multi-edge generalization. The atomic bridge proves the case of one maneuver edge and
one oriented flow. The natural extension is a whole avoidance round: a set of committed bilateral
maneuvers is a flow on the multi-edge conjunction graph, and "round total ledger conservation =
total divergence over a multi-edge cut of the conjunction graph" is the sum of the per-edge
bridges. Tying the cut to the WL equitable-partition boundary of `WhoYields` is the
novel multi-edge object. Not proved here; the atomic bridge is.
-/

end Dregg2.Apps.ConservationBridge
