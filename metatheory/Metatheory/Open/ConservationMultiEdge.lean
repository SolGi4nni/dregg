/-
# Metatheory.Open.ConservationMultiEdge — the MULTI-EDGE generalization of the Σδ=0 bridge.

This closes Part (A) of the OPEN flagged at the foot of
`Dregg2.Apps.ConservationBridge` (the multi-edge generalization comment) and ties it, as far as
is HONEST, to the WL equitable-partition boundary of `Dregg2.Apps.WhoYields` (Part B).

THE STARTING POINT (already proved, in `ConservationBridge`): the *atomic single-edge* bridge.
For ONE committed bilateral avoidance maneuver `bt : BiTurn`,
  `boundaryFlow bt = divA bt + divB bt = halfA bt + halfB bt = 0`   (`boundaryFlow_zero`),
i.e. Σδ=0 IS flow-balance across the A–B cut — one maneuver, one oriented edge.

THE OPEN (what this file does): a whole avoidance ROUND is a *set/list* of committed bilateral
maneuvers — a flow on the **multi-edge** conjunction graph. The headline:

  * **(A) CLOSED.** `round_boundaryFlow_zero` — the round's *total* cross-boundary flow over ALL
    its maneuver edges is `0`. This is the genuine multi-edge statement (an arbitrary-length sum
    over the round), obtained from the per-edge `boundaryFlow_zero` via `List.sum_eq_zero`. We
    also (i) DECOMPOSE that total into the round's total source-divergence + total
    sink-divergence (`round_flow_decomp`), making "total divergence over a multi-edge cut
    vanishes" literal; (ii) carry the *executable* CG-5 companion `round_cg5_conserves` — folding
    the bilateral turn over the whole round preserves the joint ledger total `total A + total B`;
    and (iii) name leak-freedom of the whole round (`RoundLeakFree`).

  * **(B) the WL-cut tie.** We model a round's placement on a `WhoYields.ConjGraph` by an
    embedding `Placement : BiTurn → Fin n × Fin n` (which two graph vertices each maneuver edge
    sits between). The **WL cut** is the partition boundary induced by `roleOf`: an edge *crosses*
    the cut iff its endpoints land in DIFFERENT WL cells (`G.roleOf i ≠ G.roleOf j`). We prove
    `cutFlow_zero` — the round's flow restricted to the cut-crossing maneuvers balances — and the
    SHARP tie `round_flow_is_wl_cut_flow`: under WL-discreteness on the conflict edges
    (`WhoYields.WLDiscreteOnEdges`), EVERY conflict-edge maneuver crosses the WL cut, so the
    round's WL-cut flow EQUALS its full flow, hence is `0` (`wl_cut_flow_zero_of_discrete`). The
    "symmetry boundary" of the atomic bridge is thereby the *literal WL cell boundary*, not just a
    hand-named A–B pair.

================================================================================
## HONESTY LABEL — exactly what is closed and what residual remains.
================================================================================

**CLOSED here (proved, `#assert_axioms`-clean):**
  * `round_boundaryFlow_zero` — the real multi-edge sum, NOT a single-edge restatement: it is the
    sum of `boundaryFlow` over an arbitrary `List BiTurn`. (A) is fully closed.
  * `round_flow_decomp`, `RoundLeakFree`/`round_is_leakfree`, `round_cg5_conserves`,
    `cutFlow_zero`, `round_flow_is_wl_cut_flow`, `wl_cut_flow_zero_of_discrete`.

**THE SCOPE (Part B's residual, stated precisely):**
  * `Placement` is supplied as DATA — which conjunction-graph edge each maneuver sits on. We do
    NOT derive it from the `BiTurn`'s `actorA/dstB` cell-ids (those are `CellId`s in two
    *separate* ledgers, not vertices of one shared `Fin n` conjunction graph; constructing that
    identification faithfully needs a ledger-cell ⇄ graph-vertex dictionary that is more
    scaffolding than is honest to fabricate here). Given the placement, the tie is exact: the WL
    cut IS the divergence boundary the round balances across, and under WL-discreteness it
    captures the *whole* round. The residual OPEN is therefore narrowed to: *canonically derive
    the `Placement` from the executable `BiTurn`/`ConjGraph` data* (the ledger-cell ⇄ vertex
    dictionary), after which `round_flow_is_wl_cut_flow` discharges the rest with no new ideas.
-/
import Dregg2.Apps.ConservationBridge
import Dregg2.Apps.WhoYields
import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace Metatheory.Open.ConservationMultiEdge

open Dregg2.Apps.ConservationBridge
open Dregg2.Apps.WhoYields
open Dregg2.Exec
open Dregg2.Exec.JointCell

/-! ## 1. A round = a LIST of committed bilateral maneuvers.

`BiTurn` carries no `DecidableEq` (its `amt : ℤ` field is fine, but no instance is derived), so a
round is modelled as a `List BiTurn` — a flow on the multi-edge conjunction graph, one oriented
A→B edge per maneuver. The round's **total cross-boundary flow** is the sum of the per-edge
boundary flows. -/

/-- A **round**: the committed bilateral avoidance maneuvers of one avoidance phase. -/
abbrev Round := List BiTurn

/-- The round's **total cross-boundary flow** = Σ over the round of each maneuver's
`boundaryFlow`. This is the multi-edge object: a sum over arbitrarily many oriented A→B edges. -/
def roundBoundaryFlow (round : Round) : ℤ := (round.map boundaryFlow).sum

/-! ## 2. (A) CLOSED — the round's total cross-boundary flow is ZERO. -/

/-- **`round_boundaryFlow_zero` — THE MULTI-EDGE HEADLINE.** A whole avoidance round's
*total* cross-boundary flow — summed over ALL its maneuver edges — is `0`. This is the genuine
multi-edge generalization of the atomic `boundaryFlow_zero`: not a single-edge restatement but a
sum over an arbitrary-length `Round`, discharged edge-by-edge from `boundaryFlow_zero` via
`List.sum_eq_zero`. The round's total divergence over the multi-edge cut of the conjunction graph
vanishes — Σ over the round of (value-in − value-out) is zero, the round conserves. -/
theorem round_boundaryFlow_zero (round : Round) : roundBoundaryFlow round = 0 := by
  unfold roundBoundaryFlow
  apply List.sum_eq_zero
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨bt, _, rfl⟩ := hx
  exact boundaryFlow_zero bt

/-- **`round_flow_decomp` — total flow = total source-divergence + total sink-divergence
.** The round's total cross-boundary flow splits into the sum of the maneuvers'
source-side divergences (`divA`, flow leaving) plus the sum of their sink-side divergences
(`divB`, flow entering). This makes "total divergence over a multi-edge cut" literal: the
cut-balance is exactly Σ`divA` + Σ`divB`, and `round_boundaryFlow_zero` says it is `0`. -/
theorem round_flow_decomp (round : Round) :
    roundBoundaryFlow round = (round.map divA).sum + (round.map divB).sum := by
  unfold roundBoundaryFlow
  have hmap : round.map boundaryFlow = round.map (fun bt => divA bt + divB bt) := by
    apply List.map_congr_left
    intro bt _
    rfl
  rw [hmap, List.sum_map_add]

/-- **`round_div_sum_zero` — the two cut-side totals are equal-and-opposite.** The
round's total source-divergence cancels its total sink-divergence: Σ`divA` + Σ`divB` = 0. The
multi-edge `EqualAndOpposite`: across the whole round, what leaves the source cells equals what
enters the sink cells. -/
theorem round_div_sum_zero (round : Round) :
    (round.map divA).sum + (round.map divB).sum = 0 := by
  rw [← round_flow_decomp]; exact round_boundaryFlow_zero round

/-- A round is **leak-free** iff its total cross-boundary flow is zero (nothing accumulates at the
multi-edge cut over the whole avoidance phase). -/
def RoundLeakFree (round : Round) : Prop := roundBoundaryFlow round = 0

/-- **`round_is_leakfree`.** Every round of committed maneuvers is leak-free — the
multi-edge lift of `committed_is_leakfree`. -/
theorem round_is_leakfree (round : Round) : RoundLeakFree round :=
  round_boundaryFlow_zero round

/-! ## 3. (A) the executable CG-5 companion — the round CONSERVES the joint ledger total.

The flow-balance above is the graph reading. Its OS reading: applying the whole round's bilateral
turns in sequence preserves the joint total `total A + total B`. We thread both ledger states
through the round with a fail-closed fold, and lift the single-maneuver keystone
`joint_cg5_conserves` over the list. -/

/-- **Apply a whole round** across two ledgers `A B`, atomically per maneuver and fail-closed: if
any maneuver's bilateral turn is rejected the whole round is `none`; otherwise return the final
two ledger post-states. -/
def jointApplyRound : KernelState → KernelState → Round → Option (KernelState × KernelState)
  | A, B, [] => some (A, B)
  | A, B, bt :: rest =>
    match jointApply A B bt with
    | some (A', B') => jointApplyRound A' B' rest
    | none => none

/-- **`round_cg5_conserves` — CG-5 OVER THE WHOLE ROUND.** A fully-committed avoidance
round preserves the joint ledger total `total A + total B`: each maneuver's sender-loss in one
ledger equals its receiver-gain in the other (the per-edge half-edges cancel), so the cross-side
aggregate is invariant across the entire round. The multi-edge lift of `joint_cg5_conserves`,
proved by induction on the round threading both states. This is the OS reading of
`round_boundaryFlow_zero`: balanced multi-edge flow = conserved joint ledger across the round. -/
theorem round_cg5_conserves {A B A' B' : KernelState} :
    ∀ (round : Round), jointApplyRound A B round = some (A', B') →
    jointTotal A' B' = jointTotal A B := by
  intro round
  induction round generalizing A B with
  | nil =>
    intro h
    simp only [jointApplyRound, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hA, hB⟩ := h; subst hA; subst hB; rfl
  | cons bt rest ih =>
    intro h
    unfold jointApplyRound at h
    rcases hj : jointApply A B bt with _ | ⟨A1, B1⟩ <;> rw [hj] at h
    · simp at h
    · -- conserve over the tail, then over the head maneuver: transitivity of conservation.
      rw [ih h, joint_cg5_conserves hj]

/-! ## 4. (B) Tie the cut to the WL equitable-partition boundary of `WhoYields`.

The atomic bridge named the cut "the symmetry boundary the WL refinement would place between the
two cells." Here we make that the LITERAL WL cell boundary. We place the round's maneuver edges on
a concrete `ConjGraph` and define the cut by the `roleOf` partition. -/

section WLCut

variable {n : ℕ}

/-- A **placement** of a round on the conjunction graph: which two graph vertices each maneuver's
oriented edge sits between. Supplied as DATA (the ledger-cell ⇄ graph-vertex dictionary; see the
honesty label — deriving it canonically from the `BiTurn`/`ConjGraph` is the narrowed residual). -/
abbrev Placement (n : ℕ) := BiTurn → Fin n × Fin n

/-- An edge **crosses the WL cut** iff its two endpoints lie in DIFFERENT WL cells — i.e. the WL
stable coloring gives them distinct roles. This is the equitable-partition boundary of
`WhoYields`: the cut between WL cells, the literal "symmetry boundary." -/
def crossesWLCut (G : ConjGraph n) (e : Fin n × Fin n) : Bool :=
  decide (G.roleOf e.1 ≠ G.roleOf e.2)

/-- The round's **flow across the WL cut**: the total cross-boundary flow restricted to the
maneuvers whose placed edge crosses the WL cell boundary. -/
def cutFlow (G : ConjGraph n) (place : Placement n) (round : Round) : ℤ :=
  ((round.filter (fun bt => crossesWLCut G (place bt))).map boundaryFlow).sum

/-- **`cutFlow_zero` — the round's WL-cut flow BALANCES.** The total flow carried by the
round across the WL cell boundary is `0`: it is a sub-sum of the all-zero per-edge boundary flows,
so it vanishes (`List.sum_eq_zero` over the filtered list). Divergence over the multi-edge WL cut
is conserved. -/
theorem cutFlow_zero (G : ConjGraph n) (place : Placement n) (round : Round) :
    cutFlow G place round = 0 := by
  unfold cutFlow
  apply List.sum_eq_zero
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨bt, _, rfl⟩ := hx
  exact boundaryFlow_zero bt

/-- A placement is **conflict-respecting** for a round iff every maneuver of the round is placed on
an actual conflict edge of the conjunction graph (a near-miss is a real avoidance maneuver). -/
def OnConflictEdges (G : ConjGraph n) (place : Placement n) (round : Round) : Prop :=
  ∀ bt ∈ round, G.conflict (place bt).1 (place bt).2 = true

/-- **`every_maneuver_crosses_under_discrete` — under WL-discreteness, the filter is the IDENTITY
.** If the conjunction graph is WL-discrete on its edges (`WhoYields.WLDiscreteOnEdges`:
no two conflicting sats share a role) and the round is placed on conflict edges, then EVERY
maneuver crosses the WL cut — its endpoints are in distinct WL cells. Hence filtering the round to
its cut-crossing maneuvers keeps the whole round. This is where WL rigidity meets the conservation
flow: an asymmetric scenario places every avoidance edge ACROSS the symmetry boundary. -/
theorem every_maneuver_crosses_under_discrete
    (G : ConjGraph n) (place : Placement n) (round : Round)
    (hdisc : G.WLDiscreteOnEdges) (hplace : OnConflictEdges G place round) :
    round.filter (fun bt => crossesWLCut G (place bt)) = round := by
  apply List.filter_eq_self.mpr
  intro bt hbt
  unfold crossesWLCut
  simp only [decide_eq_true_eq]
  exact hdisc (place bt).1 (place bt).2 (hplace bt hbt)

/-- **`round_flow_is_wl_cut_flow` — THE SHARP TIE.** Under WL-discreteness on the
conflict edges, the round's WL-cut flow EQUALS its full total cross-boundary flow: because every
conflict-edge maneuver crosses the cut, no maneuver is filtered out. The "symmetry boundary" the
atomic bridge named is therefore the LITERAL WL cell boundary — the cut over which the *whole*
round's divergence is measured is the WL equitable-partition boundary of `WhoYields`. -/
theorem round_flow_is_wl_cut_flow
    (G : ConjGraph n) (place : Placement n) (round : Round)
    (hdisc : G.WLDiscreteOnEdges) (hplace : OnConflictEdges G place round) :
    cutFlow G place round = roundBoundaryFlow round := by
  unfold cutFlow roundBoundaryFlow
  rw [every_maneuver_crosses_under_discrete G place round hdisc hplace]

/-- **`wl_cut_flow_zero_of_discrete` — the round balances across the WL boundary.**
Combining the sharp tie with the multi-edge headline: under WL-discreteness, the round's flow
across the literal WL cell boundary is `0`. Total ledger conservation of the whole avoidance round
= total divergence over the multi-edge WL cut of the conjunction graph — vanishing. This is the
OPEN's target statement, discharged for any conflict-respecting placement on a WL-discrete graph. -/
theorem wl_cut_flow_zero_of_discrete
    (G : ConjGraph n) (place : Placement n) (round : Round)
    (hdisc : G.WLDiscreteOnEdges) (hplace : OnConflictEdges G place round) :
    cutFlow G place round = 0 := by
  rw [round_flow_is_wl_cut_flow G place round hdisc hplace]
  exact round_boundaryFlow_zero round

end WLCut

/-! ## 7. DERIVING the placement from a ledger-cell ⇄ graph-vertex labeling (RESIDUAL PROGRESS).

Part (B) above took `Placement : BiTurn → Fin n × Fin n` as arbitrary data. Here we cut the
residual down to the ONE irreducible physical datum: a **cell labeling** `vtx : CellId → Fin n`
saying which satellite (graph vertex) each ledger cell is. The per-maneuver placement is then
DERIVED — a maneuver's oriented edge sits between the vertices of the cells it actually touches
(`srcA`, `dstB`). And, building the conjunction graph FROM the round, the conflict-respecting
condition `OnConflictEdges` is discharged BY CONSTRUCTION. The only inputs that remain are `vtx`
(a genuine deployment fact — which sat a cell belongs to) and WL-discreteness (a genuine "the
scenario is asymmetric" precondition that must NOT be faked). -/

section CanonicalPlacement
variable {n : ℕ}

/-- A **cell labeling**: the physical identification of each ledger `CellId` with a satellite
(a `ConjGraph` vertex `Fin n`). The irreducible deployment datum — which satellite a given fuel
cell belongs to. Everything downstream (placement, conflict-respecting) is derived from it. -/
abbrev CellLabeling (n : ℕ) := CellId → Fin n

/-- **The canonical placement, DERIVED from a cell labeling.** A maneuver's oriented A→B edge
sits between the vertices of its source cell `srcA` and destination cell `dstB`: not
arbitrary per-maneuver data, but `vtx` applied to the cells the `BiTurn` actually touches. -/
def canonPlacement (vtx : CellLabeling n) : Placement n :=
  fun bt => (vtx bt.srcA, vtx bt.dstB)

/-- **`canon_cutFlow_zero_of_discrete` — the WL-cut balance with the placement DERIVED from the
labeling.** `wl_cut_flow_zero_of_discrete` at `canonPlacement vtx`: under WL-discreteness,
the round's flow across the WL cell boundary vanishes, the placement now a function of the physical
labeling rather than supplied per edge. -/
theorem canon_cutFlow_zero_of_discrete
    (G : ConjGraph n) (vtx : CellLabeling n) (round : Round)
    (hdisc : G.WLDiscreteOnEdges)
    (hplace : OnConflictEdges G (canonPlacement vtx) round) :
    cutFlow G (canonPlacement vtx) round = 0 :=
  wl_cut_flow_zero_of_discrete G (canonPlacement vtx) round hdisc hplace

/-! ### Discharging `OnConflictEdges` by BUILDING the conjunction graph from the round.

The conjunction graph's edges ARE the near-misses the round maneuvers against. So we can build
`ConjGraph` directly from `(round, vtx)`: two vertices conflict iff some maneuver runs between
them. Then every maneuver is, by construction, on a conflict edge — no separate hypothesis. The
only well-formedness needed is that a maneuver connects two DISTINCT satellites (irreflexivity). -/

/-- The per-maneuver edge test: does `bt`'s placed (unordered) edge equal `{i, j}`? -/
def edgeHits (vtx : CellLabeling n) (i j : Fin n) (bt : BiTurn) : Bool :=
  (decide (vtx bt.srcA = i) && decide (vtx bt.dstB = j)) ||
  (decide (vtx bt.srcA = j) && decide (vtx bt.dstB = i))

theorem edgeHits_symm (vtx : CellLabeling n) (i j : Fin n) (bt : BiTurn) :
    edgeHits vtx i j bt = edgeHits vtx j i bt := by
  unfold edgeHits; exact Bool.or_comm _ _

/-- The conflict relation **INDUCED by a round + labeling**: `i,j` conflict iff some maneuver of
the round runs between satellites `i` and `j` (either orientation). -/
def roundConflict (vtx : CellLabeling n) (round : Round) (i j : Fin n) : Bool :=
  round.any (edgeHits vtx i j)

theorem roundConflict_symm (vtx : CellLabeling n) (round : Round) (i j : Fin n) :
    roundConflict vtx round i j = roundConflict vtx round j i := by
  unfold roundConflict
  rw [show edgeHits vtx i j = edgeHits vtx j i from funext (edgeHits_symm vtx i j)]

/-- A round is **well-formed** for a labeling iff every maneuver connects two DISTINCT satellites
(no sat is in conjunction with itself). The minimal hypothesis the irreflexive conflict needs. -/
def WellFormedRound (vtx : CellLabeling n) (round : Round) : Prop :=
  ∀ bt ∈ round, vtx bt.srcA ≠ vtx bt.dstB

theorem roundConflict_irrefl (vtx : CellLabeling n) (round : Round)
    (wf : WellFormedRound vtx round) (i : Fin n) :
    roundConflict vtx round i i = false := by
  unfold roundConflict
  rw [List.any_eq_false]
  intro bt hbt
  unfold edgeHits
  have hne : vtx bt.srcA ≠ vtx bt.dstB := wf bt hbt
  by_cases h1 : vtx bt.srcA = i
  · by_cases h2 : vtx bt.dstB = i
    · exact absurd (h1.trans h2.symm) hne
    · simp [h1, h2]
  · simp [h1]

/-- **The conjunction graph BUILT from a round + labeling.** Vertices are the `n` satellites; two
conflict iff some maneuver runs between them; symmetric and irreflexive BY CONSTRUCTION
(`roundConflict_symm`/`_irrefl`); `tag` is the operator-policy coloring carried along. -/
def roundGraph (vtx : CellLabeling n) (round : Round)
    (wf : WellFormedRound vtx round) (tag : Fin n → ℕ) : ConjGraph n where
  conflict := roundConflict vtx round
  symm := roundConflict_symm vtx round
  irrefl := roundConflict_irrefl vtx round wf
  tag := tag

/-- **`canon_onConflictEdges` — every maneuver is on a conflict edge, BY CONSTRUCTION.**
For the round-induced graph, the canonical placement of every maneuver lands on a genuine conflict
edge — witnessed by the maneuver itself. So Part (B)'s `OnConflictEdges` hypothesis is DISCHARGED,
not assumed. -/
theorem canon_onConflictEdges (vtx : CellLabeling n) (round : Round)
    (wf : WellFormedRound vtx round) (tag : Fin n → ℕ) :
    OnConflictEdges (roundGraph vtx round wf tag) (canonPlacement vtx) round := by
  intro bt hbt
  show roundConflict vtx round (vtx bt.srcA) (vtx bt.dstB) = true
  rw [roundConflict, List.any_eq_true]
  refine ⟨bt, hbt, ?_⟩
  unfold edgeHits
  simp

/-- **`round_balances_across_derived_cut` — THE NARROWED CLOSE.** Given ONLY the physical
cell labeling `vtx`, a well-formed round, operator `tag`s, AND the genuine WL-discreteness
precondition, the round's flow across the (round-induced) WL cell boundary is `0` — with the
conjunction graph, the per-maneuver placement, AND the conflict-respecting condition ALL DERIVED
from `(round, vtx, tag)`. The residual is reduced from "supply an arbitrary `Placement`" to
"supply the physical cell→satellite labeling `vtx`" (plus the irreducible WL-discreteness
hypothesis — a real scenario property). -/
theorem round_balances_across_derived_cut
    (vtx : CellLabeling n) (round : Round) (wf : WellFormedRound vtx round) (tag : Fin n → ℕ)
    (hdisc : (roundGraph vtx round wf tag).WLDiscreteOnEdges) :
    cutFlow (roundGraph vtx round wf tag) (canonPlacement vtx) round = 0 :=
  canon_cutFlow_zero_of_discrete (roundGraph vtx round wf tag) vtx round hdisc
    (canon_onConflictEdges vtx round wf tag)

end CanonicalPlacement

#assert_axioms canon_cutFlow_zero_of_discrete
#assert_axioms edgeHits_symm
#assert_axioms roundConflict_symm
#assert_axioms roundConflict_irrefl
#assert_axioms canon_onConflictEdges
#assert_axioms round_balances_across_derived_cut

/-! ## 5. `#eval` witnesses — a multi-edge round, balanced; the WL-cut tie, runnable. -/

/-- A three-maneuver avoidance round: A→B sends 30, then 12, then 7 (three oriented edges). -/
def round3 : Round :=
  [ { actorA := 0, srcA := 0, actorB := 7, dstB := 7, amt := 30, sid := 1 },
    { actorA := 1, srcA := 1, actorB := 8, dstB := 8, amt := 12, sid := 2 },
    { actorA := 2, srcA := 2, actorB := 9, dstB := 9, amt := 7,  sid := 3 } ]

#guard round3.map flowAB       == [30, 12, 7]  -- (three oriented A→B flow values)
#guard round3.map boundaryFlow == [0, 0, 0]    -- (each edge balanced)
#guard roundBoundaryFlow round3 == 0           -- (the MULTI-EDGE total cross-boundary flow)
#guard (round3.map divA).sum == -49            -- (total flow leaving the source cells)
#guard (round3.map divB).sum == 49             -- (total flow entering the sink cells)
#guard (round3.map divA).sum + (round3.map divB).sum == 0   -- (equal-and-opposite over the round)

-- The WL-cut reading on the asymmetric path `asym3` (all three sats WL-separated): place each
-- maneuver on a conflict edge (0–1, 1–2, …); every edge crosses the WL cut, so the cut flow = 0.
def placeOnAsym3 : Placement 3 := fun bt =>
  if bt.amt = 30 then (0, 1) else if bt.amt = 12 then (1, 2) else (0, 1)

#guard cutFlow ConjGraph.asym3 placeOnAsym3 round3 == 0   -- (flow across the literal WL cell boundary balances)

/-! ## 6. Axiom hygiene. -/

#assert_axioms round_boundaryFlow_zero
#assert_axioms round_flow_decomp
#assert_axioms round_div_sum_zero
#assert_axioms round_is_leakfree
#assert_axioms round_cg5_conserves
#assert_axioms cutFlow_zero
#assert_axioms every_maneuver_crosses_under_discrete
#assert_axioms round_flow_is_wl_cut_flow
#assert_axioms wl_cut_flow_zero_of_discrete

/-
RESIDUAL (narrowed OPEN). Part (A) — the multi-edge sum `round_boundaryFlow_zero`, its divergence
decomposition, leak-freedom, and the executable CG-5 round-conservation `round_cg5_conserves` — is
CLOSED. Part (B) — tying the cut to the WL equitable-partition boundary — is closed GIVEN a
`Placement` (the ledger-cell ⇄ graph-vertex dictionary): `wl_cut_flow_zero_of_discrete` shows the
round's flow across the literal WL cell boundary vanishes under WL-discreteness. The single
remaining residual is to CANONICALLY DERIVE that `Placement` from the executable `BiTurn`
(`actorA/srcA/actorB/dstB` are `CellId`s in two separate ledgers) and the `ConjGraph` vertices
(`Fin n`) — a ledger-cell ⇄ vertex identification. Once that dictionary is provided, this file's
`round_flow_is_wl_cut_flow` discharges the WL-cut balance with no further ideas.
-/

end Metatheory.Open.ConservationMultiEdge
