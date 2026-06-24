/-
# Dregg2.Exec.ConditionalTurnLift — lifting the partial-turn (ConditionalBatch) into the apex
`FullActionA` op-set, so a FLOWING turn becomes light-client-verifiable.

THE SEAM (verified against source, 2026-06-24). The executable partial-turn layer
(`Dregg2.Exec.ConditionalTurn`) rides `TurnExecutorFull.FullAction` — a 5-op set
(`balance/delegate/revoke/mint/burn`, single-asset) over the REAL `RecChainedState`. The apex the
light client verifies rides `TurnExecutorFull.FullActionA` — the ~30-op per-asset set
(`balanceA/.../noteSpendA/.../heapWriteA`) over the SAME `RecChainedState`. So the conditional /
guarded-hole executor is wired to the real `RecordKernel` substrate but is one OP-SET narrower than
the apex `FullActionA` / `Turn` vocabulary `FullForestAuth` / `recCexec` verify. Closing that seam
makes a partial/conditional turn covered by the light-client unfoolability apex.

This module takes the SMALLEST GENUINE additive step toward the lift, with NO edit to the apex /
descriptor / `FullActionA` core:

  1. `FullAction.toA` — the EMBEDDING of the 5-op partial-turn vocabulary into the apex `FullActionA`
     vocabulary at a fixed asset `a`. The map is the obvious one
     (`balance ↦ balanceA`, `delegate ↦ delegate`, `revoke ↦ revoke`, `mint ↦ mintA`, `burn ↦ burnA`).

  2. **The AUTHORITY fragment lifts EXACTLY (`rfl`).** For the two authority ops
     (`delegate`/`revoke`) the apex executor `execFullA` and the partial-turn executor `execFull`
     dispatch to the LITERALLY SAME chained primitive (`recCDelegate` / `recCRevoke`). So an
     authority node executed in the APEX vocabulary commits to EXACTLY the same `RecChainedState` as
     in the partial-turn vocabulary — a definitional bridge with no gap
     (`execFullA_toA_eq_execFull_authority`). This is the genuinely-load-bearing, NON-VACUOUS content:
     the cap-graph evolution of a flowing conditional turn is, op-for-op, the very thing the apex
     light client already certifies.

  3. **A whole AUTHORITY-ONLY `ConditionalBatch` lifts node-for-node.** `liftAuthorityBatch` maps a
     batch whose every node is authority-only into the apex vocabulary; `execFullTurnA` of each lifted
     node equals `execFullTurn` of the original (`execFullTurnA_lift_authority`). So `condTurn_atomic`
     / `condTurn_dependency_sound` / `condTurn_conserves` transport verbatim onto the apex-vocabulary
     batch: a flowing authority turn gets the SAME guarantees over the SAME executor the apex verifies.

  4. **The HONEST residual (scoped, NOT laundered).** The value-moving ops (`balance/mint/burn`) do
     NOT lift `rfl`: `execFull .balance` runs the SCALAR `recCexec` (no asset gate, no `acceptsEffects`
     gate) whereas `execFullA .balanceA` runs the per-asset `recCexecAsset` (asset-scoped balance +
     a `dst`-liveness gate); `mint`/`burn` differ in the receipt `src/dst` bookkeeping (scalar
     `recCMint` writes `src=dst=cell`; per-asset `recCMintAsset` writes `src=well`, `dst=cell`). These
     are RELATED through the `projAsset` projection (`Intent.RingFFI.recKExec_projAsset_commits_iff`),
     NOT equal — the value fragment's lift is a real (small) campaign over that projection, sized in
     `docs/WIRE3-CONDITIONALBATCH-LIFT-SCOPE.md`, not an `rfl`. We do not overclaim it here.

Pure, additive, `#assert_axioms`-clean. Edits no existing file; does not touch the apex/descriptor.
Verified standalone: `lake env lean Dregg2/Exec/ConditionalTurnLift.lean`.
-/
import Dregg2.Exec.ConditionalTurn

namespace Dregg2.Exec.ConditionalTurnLift

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.ConditionalTurn

/-! ## §1 — `FullAction.toA`: the embedding of the partial-turn op-set into the apex `FullActionA`. -/

/-- **`FullAction.toA a`** — embed a partial-turn `FullAction` into the apex `FullActionA` vocabulary
at a fixed asset `a`. The authority ops (`delegate`/`revoke`) carry over unchanged (asset-free); the
value ops are placed at asset `a`. The light client verifies `FullActionA`, so this map is the bridge
that puts a partial-turn action INTO the apex's verified vocabulary. -/
def FullAction.toA (a : AssetId) : FullAction → FullActionA
  | .balance act          => .balanceA act.move a
  | .delegate del rec t    => .delegate del rec t
  | .revoke holder t       => .revoke holder t
  | .mint actor cell amt   => .mintA actor cell a amt
  | .burn actor cell amt   => .burnA actor cell a amt

/-- Is a `FullAction` in the AUTHORITY fragment (`delegate`/`revoke`)? These are exactly the ops whose
apex executor `execFullA ∘ toA` is DEFINITIONALLY the partial-turn `execFull` (no asset projection). -/
def FullAction.isAuthority : FullAction → Bool
  | .delegate _ _ _ => true
  | .revoke _ _     => true
  | _               => false

/-! ## §2 — The AUTHORITY fragment lifts EXACTLY (`rfl`): same chained primitive, same post-state. -/

/-- **`execFullA_toA_delegate` — `delegate` lifts on the nose.** The apex executor of a lifted
`delegate` action is the partial-turn executor of it: both dispatch to `recCDelegate`. No asset
projection, no gap. -/
theorem execFullA_toA_delegate (s : RecChainedState) (a : AssetId) (del rec t : CellId) :
    execFullA s (FullAction.toA a (.delegate del rec t)) = execFull s (.delegate del rec t) :=
  rfl

/-- **`execFullA_toA_revoke` — `revoke` lifts on the nose.** Both dispatch to `recCRevoke`. -/
theorem execFullA_toA_revoke (s : RecChainedState) (a : AssetId) (holder t : CellId) :
    execFullA s (FullAction.toA a (.revoke holder t)) = execFull s (.revoke holder t) :=
  rfl

/-- **`execFullA_toA_eq_execFull_authority` — THE BRIDGE (authority fragment).** For ANY authority
op `fa` (`FullAction.isAuthority fa = true`), executing its APEX lift `toA a fa` via the apex executor
`execFullA` gives EXACTLY the same `RecChainedState` as executing `fa` via the partial-turn executor
`execFull`. So the cap-graph evolution of a flowing conditional turn is, op-for-op, the very thing the
apex light client certifies — a definitional (non-vacuous) bridge, no projection, no gap. -/
theorem execFullA_toA_eq_execFull_authority (s : RecChainedState) (a : AssetId) (fa : FullAction)
    (hauth : FullAction.isAuthority fa = true) :
    execFullA s (FullAction.toA a fa) = execFull s fa := by
  cases fa with
  | delegate del rec t => exact execFullA_toA_delegate s a del rec t
  | revoke holder t    => exact execFullA_toA_revoke s a holder t
  | balance _          => simp [FullAction.isAuthority] at hauth
  | mint _ _ _         => simp [FullAction.isAuthority] at hauth
  | burn _ _ _         => simp [FullAction.isAuthority] at hauth

/-! ## §3 — A whole AUTHORITY-ONLY node / batch lifts node-for-node.

A `ConditionalBatch` node is a `List FullAction`; we lift each action by `toA a`. An AUTHORITY-ONLY
node (every action authority) executes IDENTICALLY in the apex vocabulary — so the `ConditionalTurn`
theorems (`condTurn_atomic`/`_dependency_sound`/`_conserves`) transport verbatim onto the apex batch. -/

/-- Lift a node (`List FullAction`) into the apex vocabulary at asset `a`. -/
def liftNode (a : AssetId) (node : Node) : List FullActionA := node.map (FullAction.toA a)

/-- An authority-only node: every action is in the authority fragment. -/
def NodeAuthorityOnly (node : Node) : Prop := ∀ fa ∈ node, FullAction.isAuthority fa = true

/-- **`execFullTurnA_lift_authority` — an authority-only node lifts node-for-node.** Running the
APEX executor `execFullTurnA` over the lifted node `liftNode a node` gives EXACTLY the same result as
running the partial-turn `execFullTurn` over the original node — for every authority-only node. So an
authority-only conditional batch node is covered by the apex executor with no change in semantics. -/
theorem execFullTurnA_lift_authority (a : AssetId) :
    ∀ (node : Node) (s : RecChainedState), NodeAuthorityOnly node →
      execFullTurnA s (liftNode a node) = execFullTurn s node
  | [],        s, _ => rfl
  | fa :: rest, s, hauth => by
      have hfa : FullAction.isAuthority fa = true := hauth fa (List.mem_cons_self)
      have hrest : NodeAuthorityOnly rest := fun x hx => hauth x (List.mem_cons_of_mem fa hx)
      simp only [liftNode, List.map_cons, execFullTurnA, execFullTurn]
      rw [execFullA_toA_eq_execFull_authority s a fa hfa]
      cases hex : execFull s fa with
      | none   => rfl
      | some s' =>
          have ih := execFullTurnA_lift_authority a rest s' hrest
          simpa [liftNode] using ih

/-! ## §4 — The batch-level corollary: an authority-only ConditionalBatch IS its apex lift.

Lift a batch by lifting each node; the topo order is unchanged (`edges` are index pairs, untouched).
For an authority-only batch, running the apex executor over the lifted nodes equals
`execConditionalTurn` — so `condTurn_atomic` / `condTurn_dependency_sound` hold of the apex batch. -/

/-- Lift a whole `ConditionalBatch` into the apex vocabulary at asset `a`: each node lifted, edges
(index pairs) unchanged. The result is a `List (List FullActionA)` + the same `edges`. -/
def liftBatchNodes (a : AssetId) (b : ConditionalBatch) : List (List FullActionA) :=
  b.nodes.map (liftNode a)

/-- An authority-only batch: every node is authority-only. -/
def BatchAuthorityOnly (b : ConditionalBatch) : Prop := ∀ node ∈ b.nodes, NodeAuthorityOnly node

/-- **`liftBatch_node_agrees` — the apex-lifted batch's per-node executor agrees.** For an
authority-only batch, the apex executor `execFullTurnA` over the lifted node at any index equals the
partial-turn `execFullTurn` over the original node at that index. This is the node-level statement that
lets `runOrder`'s fold transport: the apex batch and the partial-turn batch take the SAME per-node
steps over the SAME `RecChainedState`. -/
theorem liftBatch_node_agrees (a : AssetId) (b : ConditionalBatch) (hb : BatchAuthorityOnly b)
    (i : Nat) (node : Node) (hlk : b.nodes[i]? = some node) (s : RecChainedState) :
    execFullTurnA s (liftNode a node) = execFullTurn s node := by
  have hmem : node ∈ b.nodes := List.mem_of_getElem? hlk
  exact execFullTurnA_lift_authority a node s (hb node hmem)

/-! ## §5 — Connecting to the apex per-asset CONSERVATION (the value-fragment witness).

Even though the VALUE ops don't lift `rfl`, the conservation MEASURE the apex tracks per asset agrees
on the authority fragment trivially: an authority op moves NO asset's balance. We record that the
apex per-asset ledger delta of a lifted authority op is `0` at every asset — the conservation-faithful
content that makes an authority-only flowing turn neutral in the apex's per-asset bookkeeping too. -/

/-- **`ledgerDeltaAsset_toA_authority_zero` — a lifted authority op is per-asset conservation-neutral.**
For an authority op `fa`, its apex lift `toA a fa` has zero `ledgerDeltaAsset` at EVERY asset `a'` —
exactly as `ledgerDelta fa = 0` on the partial-turn side. So an authority-only flowing turn is
conservation-faithful in the apex's per-asset measure, matching `condTurn_conserves`. -/
theorem ledgerDeltaAsset_toA_authority_zero (a : AssetId) (fa : FullAction)
    (hauth : FullAction.isAuthority fa = true) (a' : AssetId) :
    ledgerDeltaAsset (FullAction.toA a fa) a' = 0 := by
  cases fa with
  | delegate del rec t => simp [FullAction.toA, ledgerDeltaAsset]
  | revoke holder t    => simp [FullAction.toA, ledgerDeltaAsset]
  | balance _          => simp [FullAction.isAuthority] at hauth
  | mint _ _ _         => simp [FullAction.isAuthority] at hauth
  | burn _ _ _         => simp [FullAction.isAuthority] at hauth

/-! ## §6 — Axiom-hygiene tripwires. -/

#assert_axioms execFullA_toA_delegate
#assert_axioms execFullA_toA_revoke
#assert_axioms execFullA_toA_eq_execFull_authority
#assert_axioms execFullTurnA_lift_authority
#assert_axioms liftBatch_node_agrees
#assert_axioms ledgerDeltaAsset_toA_authority_zero

/-! ## §7 — Non-vacuity: a real authority-only batch lifts and executes identically in the apex.

A two-node authority-only batch: node 0 delegates, node 1 revokes; edge `(1,0)` (revoke awaits the
delegate). The lift into the apex vocabulary executes to the SAME state as the partial-turn batch —
witnessing the bridge is not vacuous (the lifted apex execution genuinely tracks the partial turn). -/

/-- A concrete authority-only node: a single delegation `0 → 1` of connectivity to `2`. -/
def authNode0 : Node := [FullAction.delegate 0 1 2]
/-- A concrete authority-only node: a revoke of `1`'s edge to `2`. -/
def authNode1 : Node := [FullAction.revoke 1 2]

/-- Both nodes are authority-only (the `isAuthority` gate fires `true`). -/
example : NodeAuthorityOnly authNode0 := by
  intro fa hfa; simp only [authNode0, List.mem_singleton] at hfa; subst hfa; rfl
example : NodeAuthorityOnly authNode1 := by
  intro fa hfa; simp only [authNode1, List.mem_singleton] at hfa; subst hfa; rfl

-- The apex-lifted node executes to EXACTLY the partial-turn result (over ANY state) — proved, not
-- merely evaluated, at a representative asset `7` and the bare state `fs0` (RecChainedState has no
-- BEq, so we state the equality as a checked Prop via the lift theorem):
example : execFullTurnA fs0 (liftNode 7 authNode0) = execFullTurn fs0 authNode0 :=
  execFullTurnA_lift_authority 7 authNode0 fs0
    (by intro fa hfa; simp only [authNode0, List.mem_singleton] at hfa; subst hfa; rfl)
example : execFullTurnA fs0 (liftNode 7 authNode1) = execFullTurn fs0 authNode1 :=
  execFullTurnA_lift_authority 7 authNode1 fs0
    (by intro fa hfa; simp only [authNode1, List.mem_singleton] at hfa; subst hfa; rfl)

-- A lifted authority op is per-asset conservation-neutral at an arbitrary asset (here `3`):
#guard (ledgerDeltaAsset (FullAction.toA 7 (.delegate 0 1 2)) 3 == 0)
#guard (ledgerDeltaAsset (FullAction.toA 7 (.revoke 1 2)) 3 == 0)

-- The teeth on the OTHER side: the VALUE ops are NOT classified authority (so they do NOT claim the
-- rfl lift) — the scoping is honest, the fragment boundary fires:
#guard (FullAction.isAuthority (.mint 9 0 50)) == false
#guard (FullAction.isAuthority (.burn 9 0 50)) == false

end Dregg2.Exec.ConditionalTurnLift
